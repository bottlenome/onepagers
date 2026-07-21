#!/usr/bin/env node
// 実モデル (deepgrove/Bonsai 1.2GB) のスモークテスト。
// SwiftShader (CPUエミュレーション) では非常に遅いので、短いプロンプト + 数トークンのみ。
// 使い方: node smoke_real.mjs [--tokens 3] [--prompt "The capital of France is"]
import { createServer } from "node:http";
import { readFileSync, statSync, existsSync, mkdirSync, copyFileSync } from "node:fs";
import { join, extname, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "..", "..");
const PORT = 8874;

// 実モデルを curl でローカルに用意 (ブラウザからは同一オリジン配信 — プロキシ/証明書問題を回避)
const RM = join(HERE, "realmodel");
mkdirSync(RM, { recursive: true });
const HF = "https://huggingface.co/deepgrove/Bonsai/resolve/main/";
for (const f of ["config.json", "model.safetensors", "tokenizer.json"]) {
  const dst = join(RM, f);
  if (f === "tokenizer.json" && !existsSync(dst) && existsSync(join(HERE, "tokenizer.json"))) {
    copyFileSync(join(HERE, "tokenizer.json"), dst);
    continue;
  }
  if (!existsSync(dst)) {
    console.log("downloading", f, "…");
    const r = spawnSync("curl", ["-sSL", "--fail", HF + f, "-o", dst + ".part"], { stdio: "inherit" });
    if (r.status !== 0) { console.error("download failed:", f); process.exit(1); }
    spawnSync("mv", [dst + ".part", dst]);
  }
}
const argv = process.argv;
const N_TOK = argv.includes("--tokens") ? Number(argv[argv.indexOf("--tokens") + 1]) : 3;
const PROMPT = argv.includes("--prompt") ? argv[argv.indexOf("--prompt") + 1] : "The capital of France is";

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

const baseUrl = `http://127.0.0.1:${PORT}/bonsai-chat/tools/realmodel/`;
await page.goto(`http://127.0.0.1:${PORT}/bonsai-chat/index.html?nocache=1&base=${encodeURIComponent(baseUrl)}`);
await page.waitForFunction(() => window.__bonsai?.ready, null, { timeout: 20000 });

const poll = setInterval(async () => {
  try {
    const p = await page.evaluate(() => window.__loadProgress);
    if (p) console.log("progress:", p);
  } catch {}
}, 5000);

console.log("エンジン初期化 + モデル読込開始 (1.2GB DL + パック)…");
const t0 = Date.now();
await page.evaluate(async () => {
  await window.__bonsai.initEngine();
  await window.__bonsai.loadModel();
});
clearInterval(poll);
console.log(`モデル読込完了: ${((Date.now() - t0) / 1000).toFixed(0)}s, GPUバッファ合計: ${await page.evaluate(() => (window.__bonsai.state.engine.gpuBytes / 1e6).toFixed(0))}MB`);

await page.evaluate((url) => window.__bonsai.loadTokenizer(url), baseUrl + "tokenizer.json");
const ids = await page.evaluate((t) => window.__bonsai.encode(t), PROMPT);
console.log(`prompt: ${JSON.stringify(PROMPT)} -> ${ids.length} tokens [${ids}]`);

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
