#!/bin/bash
set -e
set -o pipefail
set -x
if [[ $HACL_HOME == "" ]]; then
  echo "Please define HACL_HOME"
  exit 1
fi
if [[ $HACL_PACKAGES_HOME == "" ]]; then
  echo "Please define HACL_PACKAGES_HOME"
  exit 1
fi
mkdir -p wasm
cp $HACL_HOME/dist/wasm/* wasm/
cp $HACL_PACKAGES_HOME/js/* wasm/
mkdir -p js
cd js && cp ../../_build/default/js/MLS_JS.bc.js .
