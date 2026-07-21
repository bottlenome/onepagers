#!/usr/bin/env node
// bonsai-chat エンジンの数値検証 (headless Chromium + WebGPU SwiftShader)
// 両ファミリー (qllama / mlx) のフィクスチャ + 両トークナイザを検証する。
// 使い方: node test_engine.mjs
import { createServer } from "node:http";
import { readFileSync, existsSync, statSync } from "node:fs";
import { join, extname, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "..", "..");
const PORT = 8873;
const CHROMIUM = "/opt/pw-browsers/chromium";
const pwPath = process.env.PLAYWRIGHT_PKG || "/opt/node22/lib/node_modules/playwright/index.mjs";
const { chromium } = await import(pwPath);

const MIME = { ".html": "text/html", ".json": "application/json" };
const server = createServer((req, res) => {
  const path = join(ROOT, decodeURIComponent(new URL(req.url, "http://x").pathname));
  try {
    if (!statSync(path).isFile()) throw new Error("dir");
    res.setHeader("Content-Type", MIME[extname(path)] || "application/octet-stream");
    const body = readFileSync(path);
    res.setHeader("Content-Length", body.length);
    res.end(body);
  } catch { res.statusCode = 404; res.end("not found"); }
});
await new Promise((r) => server.listen(PORT, "127.0.0.1", r));

const browser = await chromium.launch({
  executablePath: CHROMIUM,
  args: ["--no-sandbox", "--enable-unsafe-webgpu", "--enable-features=Vulkan",
    "--use-webgpu-adapter=swiftshader", "--enable-unsafe-swiftshader"],
});

let failures = 0;
function check(name, cond, detail = "") {
  console.log(`${cond ? "PASS" : "FAIL"}  ${name}${detail ? "  " + detail : ""}`);
  if (!cond) failures++;
}

async function newPage(query) {
  const page = await browser.newPage();
  page.on("console", (m) => { if (m.type() === "error") console.log("[page]", m.text()); });
  page.on("pageerror", (e) => console.log("[pageerror]", e.message));
  await page.goto(`http://127.0.0.1:${PORT}/bonsai-chat/index.html?${query}`);
  await page.waitForFunction(() => window.__bonsai?.ready, null, { timeout: 20000 });
  return page;
}

// --- エンジン数値テスト (両ファミリー) ---
for (const [fam, dir] of [["qllama", "fixture"], ["mlx", "fixture-mlx"]]) {
  const expPath = join(HERE, dir, "expected.json");
  if (!existsSync(expPath)) { console.log(`SKIP ${fam} (fixture未生成)`); continue; }
  const expected = JSON.parse(readFileSync(expPath, "utf8"));
  const base = `http://127.0.0.1:${PORT}/bonsai-chat/tools/${dir}/`;
  const page = await newPage(`base=${encodeURIComponent(base)}&family=${fam}&nocache=1&notok=1`);
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
  check(`[${fam}] logits 一致`, maxAbs < 0.05, `maxAbs=${maxAbs.toExponential(2)} refMax=${refMax.toFixed(2)}`);
  check(`[${fam}] argmax 一致`, argmaxJs === argmaxRef, `js=${argmaxJs} ref=${argmaxRef}`);
  const greedy = await page.evaluate(
    ({ ids, n }) => window.__bonsai.greedy(ids, n),
    { ids: expected.prompt_ids, n: expected.greedy_ids.length });
  check(`[${fam}] greedy 系列一致`, JSON.stringify(greedy) === JSON.stringify(expected.greedy_ids),
    `js=[${greedy}] ref=[${expected.greedy_ids}]`);
  await page.close();
}

// --- トークナイザテスト ---
for (const [type, tokFile, vecFile] of [
  ["sp", "tokenizer.json", "token_vectors.json"],
  ["bl", "qwen_tokenizer.json", "qwen_token_vectors.json"],
]) {
  if (!existsSync(join(HERE, tokFile)) || !existsSync(join(HERE, vecFile))) {
    console.log(`SKIP tokenizer ${type} (${tokFile} か ${vecFile} が無い)`);
    continue;
  }
  const vectors = JSON.parse(readFileSync(join(HERE, vecFile), "utf8"));
  const page = await newPage("nocache=1&notok=1");
  await page.evaluate(({ url, type }) => window.__bonsai.loadTokenizer(url, type),
    { url: `http://127.0.0.1:${PORT}/bonsai-chat/tools/${tokFile}`, type });
  for (const v of vectors) {
    const ids = await page.evaluate((t) => window.__bonsai.encode(t), v.text);
    const dec = await page.evaluate((ids) => window.__bonsai.decode(ids), v.ids);
    const okE = JSON.stringify(ids) === JSON.stringify(v.ids);
    const okD = dec === v.decoded;
    check(`[${type}] encode ${JSON.stringify(v.text.slice(0, 25))}`, okE,
      okE ? "" : `js=[${ids.slice(0, 12)}] ref=[${v.ids.slice(0, 12)}]`);
    check(`[${type}] decode ${JSON.stringify(v.text.slice(0, 25))}`, okD,
      okD ? "" : `js=${JSON.stringify(dec.slice(0, 40))} ref=${JSON.stringify(v.decoded.slice(0, 40))}`);
  }
  await page.close();
}

await browser.close();
server.close();
console.log(failures === 0 ? "\nALL PASS" : `\n${failures} FAILURES`);
process.exit(failures === 0 ? 0 : 1);
