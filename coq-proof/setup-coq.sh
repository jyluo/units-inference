#!/bin/bash

# Fail the whole script if any command fails
set -e

myDir="`dirname $0`"
case `uname -s` in
    CYGWIN*)
      myDir=`cygpath -m $mydir`
      ;;
esac

if [ "$myDir" = "" ];
then
    myDir="."
fi

ROOT=$(cd ${myDir} && pwd)

# install dependencies
echo "Installing ocaml and camlp5 packages via sudo apt-get, enter password if prompted"
sudo apt-get install ocaml camlp5

COQ_TAR_FILE=V8.8.2.tar.gz

# download coq sources
if [ -e $ROOT/$COQ_TAR_FILE ] ; then
    echo "Found existing $COQ_TAR_FILE in $ROOT, skip downloading sources."
else
    echo "Downloading $COQ_TAR_FILE from github ..."
    wget "https://github.com/coq/coq/archive/${COQ_TAR_FILE}"
    echo "Downloaded $COQ_TAR_FILE from github"
fi

# extract coq sources into $ROOT/coq-source
if [ ! -d $ROOT/coq-source ] ; then
    mkdir $ROOT/coq-source
fi
if [ ! -e $ROOT/coq-source/Makefile ] ; then
    echo "Extracting sources to $ROOT/coq-source"
    tar -xzf $COQ_TAR_FILE
    mv $ROOT/coq-*/* $ROOT/coq-source
fi

# install coq locally
cd $ROOT/coq-source

if [ ! -e $ROOT/coq-source/bin/coqc ] ; then
    echo "Configuring coq for local installation"
    ./configure -local

    echo "Compiling coq"
    make
fi

# test coqc
echo "Coq installed at $ROOT/coq-source/bin/coqc"
./bin/coqc -v
