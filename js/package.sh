#!/bin/sh
cd .. && find js -type f -not -iname import.sh -and -not -iname dune -and -not -iname '*.ts' -and -not -iname index.html  -and -not -iname '.*' | xargs tar cjvf mls-$(date +%Y%m%d%H%M).tar.bz2
