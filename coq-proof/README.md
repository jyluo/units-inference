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

`TacticalLemmas.v` contains tactic notations from the Software Foundations Coq [Library](http://flint.cs.yale.edu/cs428/coq/sf/SfLib.html), which helps break down proof cases.

`Maps.v` contains the definitions and helper lemmas for maps from any key type `K` to any value type `V`, augmented by a key equality function `key_eq`.

`Units.v` contains the definitions and helper lemmas for the unit types <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{T}}" title="T"/> .

`LabeledLiterals.v` contains the definitions and helper lemmas for labeled literals <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{l%20=%20T_{v}\%20z}}" title="l = Tv z"/> (static semantics) / labeled values <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{T_{l}\%20z}}" title="Tl z"/> (operational semantics), which are modeled as nats labeled with a unit in Coq.

`IDs.v` contains the definitions and helper lemmas for variable identifiers <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{v}}" title="v"/>.

`Gamma.v` defines gamma as a map from <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{v}}" title="v"/> to <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{T}}" title="T"/>, using the map definitions from `Maps.v`.

`StackFrame.v` defines Stack Frame <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{F}}" title="F"/> as a map from <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{v}}" title="v"/> to its static type <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{T_{v}}}" title="Tv"/> and labeled value <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{T_{l}\%20z}}" title="Tl z"/>, using the map definitions from `Maps.v`.

`Subtyping.v` contains the definitions and helper lemmas for the subtype relationship between units types, and functions such as the least upper bound of units.

`GammaStackFrameCorrespondence.v` defines the correspondince between a wellformed gamma and a wellformed stack frame.

`UnitsArithmetics.v` defines and proves properties for the arithmetic functions add, multiply, and modulo between units; including the subtype consistent lemmas discussed in the paper.

`VarDecls.v` contains the definitions and the proof of progress and preservation helper lemmas for variable declarations <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{vd}}" title="vd"/> in our language.

`Expressions.v` contains the definitions and the proof of progress and preservation helper lemmas for expressions <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{e}}" title="e"/> in our language.

`Statements.v` contains the definitions and the proof of progress and preservation helper lemmas for assignment statements <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{s}}" title="s"/> in our language.

`Program.v` contains the definitions for programs <img src="https://latex.codecogs.com/svg.latex?\ensuremath{\mathit{P}}" title="P"/> in our language, and the overall proof of progress and preservation lemmas.
