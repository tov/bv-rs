#!/bin/sh

DESTDIR="`pwd`"/kcov-build

if ! [ -d "$DESTDIR" ]; then
    wget https://github.com/SimonKagstrom/kcov/archive/master.tar.gz || exit 1

    tar xzf master.tar.gz
    cd kcov-master

    mkdir build
    cd build

    cmake .. || exit 2
    make || exit 3
    make install DESTDIR="$DESTDIR"

    cd ../..

    rm -Rf kcov-master
fi

for file in target/debug/bv-*[^\.d]; do
    COVDIR="target/cov/$(basename $file)"
    mkdir -p "$COVDIR"
    "$DESTDIR"/usr/local/bin/kcov --exclude-pattern=/.cargo,/usr/lib --verify "$COVDIR" "$file"
done

bash <(curl -s https://codecov.io/bash) || exit 4

echo "Uploaded code coverage"
