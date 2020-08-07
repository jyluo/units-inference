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

# use system installed coqc if available
# if version dependent: && [[ $(coqc -v | grep 8.8.0) ]]
if [[ $(command -v coqc) ]] ; then
    COQC=$(command -v coqc)
fi
if [ -z "$COQC" ] && [ -e $ROOT/coq-source/bin/coqc ] ; then
    COQC="$ROOT/coq-source/bin/coqc"
fi
echo "Using coqc at $COQC"
$COQC -v

function compile() {
  local target=$1
  echo "Compiling ${target}"
  $COQC $target -Q $ROOT PUnits 2>&1
}

compile TacticalLemmas.v
compile Maps.v

compile Units.v
compile LabeledLiterals.v

compile IDs.v

compile Gamma.v
compile StackFrame.v

compile Subtyping.v
compile GammaStackFrameCorrespondence.v

compile UnitsArithmetics.v

compile VarDecls.v
compile Expressions.v
compile Statements.v
compile Program.v

echo "Compilation complete."
