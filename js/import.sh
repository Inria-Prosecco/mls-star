#!/usr/bin/env bash
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

declare -a HACL_MODULES
HACL_MODULES=(
  WasmSupport
  FStar
  LowStar_Endianness
  Hacl_Hash_Base
  Hacl_Hash_MD5
  Hacl_Hash_SHA1
  Hacl_Hash_SHA2
  Hacl_Impl_Blake2_Constants
  Hacl_Hash_Blake2s
  Hacl_Hash_Blake2b
  Hacl_HMAC
  Hacl_HKDF
  Hacl_Bignum_Base
  Hacl_Bignum
  Hacl_Bignum25519_51
  Hacl_Curve25519_51
  Hacl_Ed25519_PrecompTable
  Hacl_Ed25519
  Hacl_EC_Ed25519
  Hacl_Chacha20
  Hacl_Chacha20_Vec32
  Hacl_MAC_Poly1305
  Hacl_AEAD_Chacha20Poly1305
)

for m in ${HACL_MODULES[@]}; do
  cp $HACL_HOME/dist/wasm/$m.wasm wasm/
done
cp $HACL_HOME/dist/wasm/*.js* wasm/
cp $HACL_PACKAGES_HOME/js/* wasm/
mkdir -p js
rm -rf js/MLS_JS.bc.js
cp ../_build/default/js/MLS_JS.bc.js js/
