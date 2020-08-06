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

$COQC TacticalLemmas.v
$COQC IDDefs.v
$COQC MapsDefs.v

$COQC UnitsDefs.v

$COQC ValueDefs.v
$COQC GammaDefs.v
$COQC HeapDefs.v
$COQC SubtypingDefs.v
$COQC GammaHeapCorrespondence.v

$COQC UnitsArithmetics.v

$COQC FieldDefs.v
$COQC ExpressionDefs.v
$COQC StatementDefs.v
$COQC ProgramDefs.v

echo "Compilation complete."
