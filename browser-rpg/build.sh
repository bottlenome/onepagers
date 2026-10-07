#!/bin/bash
# Loveless Chronicle ビルドスクリプト
# src/ 以下のファイルを結合して index.html を生成する
set -euo pipefail
cd "$(dirname "$0")"

OUT="index.html"

cat <<'HTMLHEAD' > "$OUT"
<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
<title>Loveless Chronicle - OnePagers</title>
<style>
HTMLHEAD

cat src/css/style.css >> "$OUT"

cat <<'HTMLMID' >> "$OUT"
</style>
</head>
<body>
<div id="app">
  <header id="hdr"></header>
  <main id="main"></main>
  <footer id="log"></footer>
</div>
<script>
'use strict';
HTMLMID

# --- Data ---
cat src/data/constants.js >> "$OUT"
cat src/data/jobs.js      >> "$OUT"
cat src/data/skills.js    >> "$OUT"
cat src/data/equips.js    >> "$OUT"
cat src/data/items.js     >> "$OUT"
cat src/data/monsters.js  >> "$OUT"
cat src/data/areas.js     >> "$OUT"
cat src/data/shops.js     >> "$OUT"
cat src/data/recipes.js   >> "$OUT"
cat src/data/arena.js     >> "$OUT"

# --- Engine ---
cat src/engine/state.js      >> "$OUT"
cat src/engine/stats.js      >> "$OUT"
cat src/engine/combat.js     >> "$OUT"
cat src/engine/economy.js    >> "$OUT"
cat src/engine/crafting.js   >> "$OUT"
cat src/engine/navigation.js >> "$OUT"
cat src/engine/save.js       >> "$OUT"

# --- UI ---
cat src/ui/components.js >> "$OUT"
cat src/ui/screens.js    >> "$OUT"
cat src/ui/events.js     >> "$OUT"
cat src/ui/render.js     >> "$OUT"

# --- Plugins ---
cat src/plugins/social.js >> "$OUT"

# --- Main ---
cat src/main.js >> "$OUT"

cat <<'HTMLFOOT' >> "$OUT"
</script>
<p data-onepagers-privacy style="margin:1rem auto;padding:0 .75rem;text-align:center;font-size:.75rem;line-height:1.6;color:#94a3b8">アクセス解析: Cloudflare（Cookie 不使用） · <a href="../privacy.html" style="color:#7dd3fc" target="_blank" rel="noopener">送信する情報と対象ページ</a></p>
<script defer src="../analytics.js"></script>
</body></html>
HTMLFOOT

echo "✓ Built $OUT ($(wc -c < "$OUT") bytes)"
