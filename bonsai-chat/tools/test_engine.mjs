#!/usr/bin/env node
// bonsai-chat エンジンの数値検証 (headless Chromium + WebGPU SwiftShader)
// 使い方: node test_engine.mjs [--chromium /path/to/chromium]
import { createServer } from "node:http";
import { readFileSync, existsSync, statSync } from "node:fs";
import { join, extname, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "..", "..");
const PORT = 8873;
const CHROMIUM = process.argv.includes("--chromium")
  ? process.argv[process.argv.indexOf("--chromium") + 1]
  : "/opt/pw-browsers/chromium";

const pwPath = process.env.PLAYWRIGHT_PKG || "/opt/node22/lib/node_modules/playwright/index.mjs";
const { chromium } = await import(pwPath);

const MIME = { ".html": "text/html", ".json": "application/json", ".safetensors": "application/octet-stream" };
const server = createServer((req, res) => {
  const path = join(ROOT, decodeURIComponent(new URL(req.url, "http://x").pathname));
  try {
    if (!statSync(path).isFile()) throw new Error("dir");
    res.setHeader("Content-Type", MIME[extname(path)] || "application/octet-stream");
    const body = readFileSync(path);
    res.setHeader("Content-Length", body.length);
    res.end(body);
  } catch {
    res.statusCode = 404;
    res.end("not found");
  }
});
await new Promise((r) => server.listen(PORT, "127.0.0.1", r));

const expected = JSON.parse(readFileSync(join(HERE, "fixture", "expected.json"), "utf8"));
const hasTok = existsSync(join(HERE, "tokenizer.json"));
const vectors = existsSync(join(HERE, "token_vectors.json"))
  ? JSON.parse(readFileSync(join(HERE, "token_vectors.json"), "utf8"))
  : null;

const browser = await chromium.launch({
  executablePath: CHROMIUM,
  args: ["--no-sandbox", "--enable-unsafe-webgpu", "--enable-features=Vulkan",
    "--use-webgpu-adapter=swiftshader", "--enable-unsafe-swiftshader"],
});
const page = await browser.newPage();
page.on("console", (m) => { if (m.type() === "error" || m.type() === "warning") console.log("[page]", m.type(), m.text()); });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));

const base = `http://127.0.0.1:${PORT}/bonsai-chat/tools/fixture/`;
await page.goto(`http://127.0.0.1:${PORT}/bonsai-chat/index.html?base=${encodeURIComponent(base)}&nocache=1&notok=1`);
await page.waitForFunction(() => window.__bonsai?.ready, null, { timeout: 20000 });

let failures = 0;
function check(name, cond, detail = "") {
  console.log(`${cond ? "PASS" : "FAIL"}  ${name}${detail ? "  " + detail : ""}`);
  if (!cond) failures++;
}

// --- エンジン数値テスト ---
await page.evaluate(async () => { await window.__bonsai.initEngine(); await window.__bonsai.loadModel(); });
const logits = await page.evaluate((ids) => window.__bonsai.forwardTokens(ids), expected.prompt_ids);
const ref = expected.logits_after_prompt;
let maxAbs = 0, refMax = 0;
for (let i = 0; i < ref.length; i++) {
  maxAbs = Math.max(maxAbs, Math.abs(logits[i] - ref[i]));
  refMax = Math.max(refMax, Math.abs(ref[i]));
}
const argmaxJs = logits.indexOf(Math.max(...logits));
const argmaxRef = ref.indexOf(Math.max(...ref));
check("logits 一致 (maxAbsDiff)", maxAbs < 0.05, `maxAbs=${maxAbs.toExponential(2)} refMax=${refMax.toFixed(2)}`);
check("argmax 一致", argmaxJs === argmaxRef, `js=${argmaxJs} ref=${argmaxRef}`);

const greedy = await page.evaluate(
  ({ ids, n }) => window.__bonsai.greedy(ids, n),
  { ids: expected.prompt_ids, n: expected.greedy_ids.length }
);
check("greedy 系列一致", JSON.stringify(greedy) === JSON.stringify(expected.greedy_ids),
  `js=[${greedy}] ref=[${expected.greedy_ids}]`);

// --- トークナイザテスト ---
if (hasTok && vectors) {
  await page.evaluate((url) => window.__bonsai.loadTokenizer(url), `http://127.0.0.1:${PORT}/bonsai-chat/tools/tokenizer.json`);
  for (const v of vectors) {
    const ids = await page.evaluate((t) => window.__bonsai.encode(t), v.text);
    const dec = await page.evaluate((ids) => window.__bonsai.decode(ids), v.ids);
    check(`encode ${JSON.stringify(v.text.slice(0, 25))}`, JSON.stringify(ids) === JSON.stringify(v.ids),
      JSON.stringify(ids) === JSON.stringify(v.ids) ? "" : `js=[${ids.slice(0, 12)}] ref=[${v.ids.slice(0, 12)}]`);
    check(`decode ${JSON.stringify(v.text.slice(0, 25))}`, dec === v.decoded,
      dec === v.decoded ? "" : `js=${JSON.stringify(dec.slice(0, 40))} ref=${JSON.stringify(v.decoded.slice(0, 40))}`);
  }
} else {
  console.log("SKIP tokenizer tests (tools/tokenizer.json か token_vectors.json が無い)");
}

await browser.close();
server.close();
console.log(failures === 0 ? "\nALL PASS" : `\n${failures} FAILURES`);
process.exit(failures === 0 ? 0 : 1);
