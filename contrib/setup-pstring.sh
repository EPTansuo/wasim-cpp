#!/bin/bash

PSTRING_VERSION=457531cbbe50ab29a4342e4c32bbc94a034aff04

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/pstring" ]; then
    cd $DEPS
    git clone git@github.com:EPTansuo/PString.git pstring
    cd pstring
    git checkout -f $STRING_VERSION
    mkdir build 
    cd build
    cmake .. -DCMAKE_INSTALL_PREFIX=/usr 
		make && sudo make install  # I will modified it later to avoid `sudo`
    cd $DIR
else
    echo "$DEPS/pstring already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/pstring/lib/libpstring.so ] ; then \
    echo "It appears PString was successfully built in $DEPS/pstring/lib."
    echo "You may now build wasim with: ./configure.sh && cd build && make"
else
    echo "Building PString failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/EPTansuo/PString"
    exit 1
fi

