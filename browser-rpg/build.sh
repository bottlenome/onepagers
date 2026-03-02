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

echo '</script></body></html>' >> "$OUT"

echo "✓ Built $OUT ($(wc -c < "$OUT") bytes)"
