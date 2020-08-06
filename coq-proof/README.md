The scripts contained in this folder were tested on ubuntu 20.04 LTS, it is intended to be run on linux.

### Dependencies

Coq v8.11.0

### Check pUnits proofs

run `./compile.sh`

### Interactively check pUnits proofs

run `./openCoqIDE.sh` to open the proof files in CoqIDE in their dependent ordering.

### Clean up

run `./cleanup.sh` to remove coq output files

## Proof file structure

`TacticalLemmas.v` contains tactic notations from the Software Foundations Coq [Library](http://flint.cs.yale.edu/cs428/coq/sf/SfLib.html), which helps break down proof cases.

`Maps.v` contains the definitions and lemmas for maps from any key type `K` to value type `V`, augmented by a key equality function `key_eq`.

`UnitsDefs.v` contains the definitions and lemmas for the unit types **_T_**.

`ValueDefs.v` contains the definitions and lemmas for labeled values **_v_**, which are modeled as nats labeled with a unit in Coq.

`IDDefs.v` contains the definitions and lemmas for field identifiers **_f_**.

`GammaDefs.v` defines gamma as a map from **_f_** to **_T_**, using the map definitions from `Maps.v`.

`HeapDefs.v` defines heap as a map from **_f_** to its static field type **_Tf_** and runtime value **_v_**, using the map definitions from `Maps.v`.

`SubtypingDefs.v` contains the definitions and lemmas for the subtype relationship between units qualifiers, and functions such as the least upper bound of units.

`GammaHeapCorrespondence.v` defines the correspondince between a wellformed gamma and a wellformed heap.

`UnitsArithmetics.v` defines and proves properties for the arithmetic functions add, multiply, and modulo between units; including the subtype consistent lemmas discussed in the paper.

`FieldDefs.v` contains the definitions and the proof of progress and preservation helper lemmas for field declarations **_fd_** in our language.

`ExpressionDefs.v` contains the definitions and the proof of progress and preservation helper lemmas for expressions **_e_** in our language.

`StatementDefs.v` contains the definitions and the proof of progress and preservation helper lemmas for assignment statements **_s_** in our language.

`ProgramDefs.v` contains the definitions for programs **_P_** in our language, and the overall proof of progress and preservation lemmas.
