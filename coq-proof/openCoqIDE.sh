#!/bin/bash

# Opens the definitions in their dependent ordering, where
# later file names in the sequence depend on the earlier ones.
coqide TacticalLemmas.v \
  Maps.v \
  Units.v \
  LabeledLiterals.v \
  IDs.v \
  Gamma.v \
  StackFrame.v \
  Subtyping.v \
  GammaStackFrameCorrespondence.v \
  UnitsArithmetics.v \
  VarDecls.v \
  Expressions.v \
  Statements.v \
  Program.v \
  &
