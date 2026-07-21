#!/usr/bin/env node
// 実モデルのスモークテスト。curl でローカルに取得し同一オリジン配信して実行する。
// SwiftShader (CPUエミュレーション) では非常に遅いので、短いプロンプト + 数トークンのみ。
// 使い方:
//   node smoke_real.mjs                    # deepgrove Bonsai 0.5B (1.2GB)
//   node smoke_real.mjs --model tb17       # Ternary Bonsai 1.7B mlx-2bit (0.48GB)
//   node smoke_real.mjs --tokens 5 --prompt "..."
import { createServer } from "node:http";
import { readFileSync, statSync, existsSync, mkdirSync } from "node:fs";
import { join, extname, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "..", "..");
const PORT = 8874;
const argv = process.argv;
const arg = (name, dflt) => argv.includes(name) ? argv[argv.indexOf(name) + 1] : dflt;
const MODEL = arg("--model", "deepgrove");
const N_TOK = Number(arg("--tokens", MODEL === "deepgrove" ? "3" : "8"));

const SPECS = {
  deepgrove: {
    dir: "realmodel", family: "qllama",
    hf: "https://huggingface.co/deepgrove/Bonsai/resolve/main/",
    prompt: arg("--prompt", "The capital of France is"),
    buildIds: (page, base, prompt) => page.evaluate((t) => window.__bonsai.encode(t), prompt),
    tokType: "sp",
  },
  tb17: {
    dir: "realmodel-tb17", family: "mlx",
    hf: "https://huggingface.co/prism-ml/Ternary-Bonsai-1.7B-mlx-2bit/resolve/main/",
    prompt: arg("--prompt", "<|im_start|>user\nWhat is the capital of France? Answer in one word.<|im_end|>\n<|im_start|>assistant\n<think>\n\n</think>\n\n"),
    buildIds: (page, base, prompt) => page.evaluate((t) => window.__bonsai.encode(t), prompt),
    tokType: "bl",
  },
};
const spec = SPECS[MODEL];
if (!spec) { console.error("unknown --model:", MODEL); process.exit(1); }

// モデルファイルを curl で用意
const RM = join(HERE, spec.dir);
mkdirSync(RM, { recursive: true });
for (const f of ["config.json", "model.safetensors", "tokenizer.json"]) {
  const dst = join(RM, f);
  if (!existsSync(dst)) {
    console.log("downloading", f, "…");
    const r = spawnSync("curl", ["-sSL", "--fail", spec.hf + f, "-o", dst + ".part"], { stdio: "inherit" });
    if (r.status !== 0) { console.error("download failed:", f); process.exit(1); }
    spawnSync("mv", [dst + ".part", dst]);
  }
}

const pwPath = process.env.PLAYWRIGHT_PKG || "/opt/node22/lib/node_modules/playwright/index.mjs";
const { chromium } = await import(pwPath);

const server = createServer((req, res) => {
  const path = join(ROOT, decodeURIComponent(new URL(req.url, "http://x").pathname));
  try {
    if (!statSync(path).isFile()) throw new Error("dir");
    res.setHeader("Content-Type", extname(path) === ".html" ? "text/html" : "application/octet-stream");
    res.end(readFileSync(path));
  } catch { res.statusCode = 404; res.end(); }
});
await new Promise((r) => server.listen(PORT, "127.0.0.1", r));

const browser = await chromium.launch({
  executablePath: "/opt/pw-browsers/chromium",
  args: ["--no-sandbox", "--enable-unsafe-webgpu", "--enable-features=Vulkan",
    "--use-webgpu-adapter=swiftshader", "--enable-unsafe-swiftshader"],
});
const page = await browser.newPage();
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
page.on("console", (m) => { if (m.type() === "error") console.log("[page]", m.text()); });

const baseUrl = `http://127.0.0.1:${PORT}/bonsai-chat/tools/${spec.dir}/`;
await page.goto(`http://127.0.0.1:${PORT}/bonsai-chat/index.html?nocache=1&base=${encodeURIComponent(baseUrl)}&family=${spec.family}`);
await page.waitForFunction(() => window.__bonsai?.ready, null, { timeout: 20000 });

const poll = setInterval(async () => {
  try {
    const p = await page.evaluate(() => window.__loadProgress);
    if (p) console.log("progress:", p);
  } catch {}
}, 5000);

console.log(`[${MODEL}] エンジン初期化 + モデル読込開始…`);
const t0 = Date.now();
await page.evaluate(async () => {
  await window.__bonsai.initEngine();
  await window.__bonsai.loadModel();
});
clearInterval(poll);
console.log(`モデル読込完了: ${((Date.now() - t0) / 1000).toFixed(0)}s, GPUバッファ合計: ${await page.evaluate(() => (window.__bonsai.state.engine.gpuBytes / 1e6).toFixed(0))}MB`);

await page.evaluate(({ url, type }) => window.__bonsai.loadTokenizer(url, type),
  { url: baseUrl + "tokenizer.json", type: spec.tokType });
const ids = await spec.buildIds(page, baseUrl, spec.prompt);
console.log(`prompt: ${JSON.stringify(spec.prompt.slice(0, 80))} -> ${ids.length} tokens`);

console.log(`greedy ${N_TOK} tokens 生成中 (SwiftShaderなので低速)…`);
const t1 = Date.now();
const out = await page.evaluate(({ ids, n }) => window.__bonsai.greedy(ids, n), { ids, n: N_TOK });
const dt = (Date.now() - t1) / 1000;
const text = await page.evaluate((ids) => window.__bonsai.decode(ids), out);
console.log(`生成: [${out}] -> ${JSON.stringify(text)}`);
console.log(`所要 ${dt.toFixed(1)}s (${((ids.length + N_TOK) / dt).toFixed(2)} tok/s on SwiftShader)`);

await browser.close();
server.close();
console.log("SMOKE OK");
