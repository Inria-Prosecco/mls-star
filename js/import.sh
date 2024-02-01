mkdir -p wasm
cp $HACL_HOME/dist/wasm/* wasm/
cp $HACL_PACKAGES_HOME/js/* wasm/
mkdir -p js
(cd js && ln -s ../../_build/default/js/MLS_JS.bc.js)
