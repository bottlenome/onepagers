#!/bin/bash
# Build: src/ -> index.html
set -e
cd "$(dirname "$0")"

CSS=$(cat src/css/style.css)
JS_CONST=$(cat src/data/constants.js)
JS_CANVAS=$(cat src/js/canvas-utils.js)
JS_SIMA=$(cat src/js/sim-a-theta-link.js)
JS_SIMB=$(cat src/js/sim-b-indeterminacy.js)
JS_SIMC=$(cat src/js/sim-c-logshell.js)
JS_SIMD=$(cat src/js/sim-d-abc.js)
JS_MAIN=$(cat src/js/main.js)

sed \
  -e "/\/\* __CSS__ \*\//r src/css/style.css" \
  -e "s|/\* __CSS__ \*/||" \
  -e "/\/\* __JS_CONSTANTS__ \*\//r src/data/constants.js" \
  -e "s|/\* __JS_CONSTANTS__ \*/||" \
  -e "/\/\* __JS_CANVAS__ \*\//r src/js/canvas-utils.js" \
  -e "s|/\* __JS_CANVAS__ \*/||" \
  -e "/\/\* __JS_SIMA__ \*\//r src/js/sim-a-theta-link.js" \
  -e "s|/\* __JS_SIMA__ \*/||" \
  -e "/\/\* __JS_SIMB__ \*\//r src/js/sim-b-indeterminacy.js" \
  -e "s|/\* __JS_SIMB__ \*/||" \
  -e "/\/\* __JS_SIMC__ \*\//r src/js/sim-c-logshell.js" \
  -e "s|/\* __JS_SIMC__ \*/||" \
  -e "/\/\* __JS_SIMD__ \*\//r src/js/sim-d-abc.js" \
  -e "s|/\* __JS_SIMD__ \*/||" \
  -e "/\/\* __JS_MAIN__ \*\//r src/js/main.js" \
  -e "s|/\* __JS_MAIN__ \*/||" \
  src/template.html > index.html

echo "Built index.html ($(wc -c < index.html) bytes)"
