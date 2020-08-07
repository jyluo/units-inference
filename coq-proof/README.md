The scripts contained in this folder were tested on ubuntu 20.04 LTS, it is intended to be run on linux.

### Dependencies

Coq v8.11.0

### Check pUnits proofs

run `./compile.sh`.

### Interactively check pUnits proofs

run `./openCoqIDE.sh` to open the proof files in CoqIDE in their dependent ordering.

### Clean up

run `./cleanup.sh` to remove Coq output files.

## Proof file structure

#TODO use <img src="https://latex.codecogs.com/svg.latex?\Large&space;x=\frac{-b\pm\sqrt{b^2-4ac}}{2a}" title="\Large x=\frac{-b\pm\sqrt{b^2-4ac}}{2a}" />  to get latex symbols.

`TacticalLemmas.v` contains tactic notations from the Software Foundations Coq [Library](http://flint.cs.yale.edu/cs428/coq/sf/SfLib.html), which helps break down proof cases.

`Maps.v` contains the definitions and helper lemmas for maps from any key type `K` to any value type `V`, augmented by a key equality function `key_eq`.

`Units.v` contains the definitions and helper lemmas for the unit types **_T_**.

`LabeledLiterals.v` contains the definitions and helper lemmas for labeled literals (static semantics) / labeled values (operational semantics) **_l_**, which are modeled as nats labeled with a unit in Coq.

`IDs.v` contains the definitions and helper lemmas for variable identifiers **_v_**.

`Gamma.v` defines gamma as a map from **_v_** to **_T_**, using the map definitions from `Maps.v`.

`StackFrame.v` defines Stack Frame **_F_** as a map from **_v_** to its static type **_Tv_** and labeled value **_l_**, using the map definitions from `Maps.v`.

`Subtyping.v` contains the definitions and helper lemmas for the subtype relationship between units types, and functions such as the least upper bound of units.

`GammaStackFrameCorrespondence.v` defines the correspondince between a wellformed gamma and a wellformed stack frame.

`UnitsArithmetics.v` defines and proves properties for the arithmetic functions add, multiply, and modulo between units; including the subtype consistent lemmas discussed in the paper.

`VarDecls.v` contains the definitions and the proof of progress and preservation helper lemmas for variable declarations **_vd_** in our language.

`Expressions.v` contains the definitions and the proof of progress and preservation helper lemmas for expressions **_e_** in our language.

`Statements.v` contains the definitions and the proof of progress and preservation helper lemmas for assignment statements **_s_** in our language.

`Program.v` contains the definitions for programs **_P_** in our language, and the overall proof of progress and preservation lemmas.
