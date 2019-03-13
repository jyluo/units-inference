open UnitsTestMultiModule.HelperLib

[<Measure>] type km
[<Measure>] type h
[<Measure>] type s

// constants for testing type system
let d = 30<km>
let t1 = 10<h>
let t2 = 10<s>
let e = 10<1>   // same as dimensionless int by itself

// calling a function from another module, the parameter types are assumed to be dimensionless integers
// let speedError = calcSpeed(d,t) // compile time error
let s1 = calcSpeed(e,e)  // ok

// calling a function explicitly annotated as polymorphic is ok
let s1Poly = calcSpeedPoly(d,t1)  // ok

// lets also define a local copy of both methods found in HelperLib
let localCalcSpeed (dist, time) = dist / time
let localCalcSpeedPoly (dist:int<_>, time:int<_>) = dist / time

// calling the local unannotated copy is ok, F# type inference infers the units of the function parameters and returns
let s2 = localCalcSpeed(d, t1)

let s2BadCall = localCalcSpeed(d, t2)   // error issued here, the type signature of localCalcSpeed is already unified iwth the call for variable s2, and cannot unify with this call

// calling the local polymorphic annotated copy is also ok
let lSpeedPoly = localCalcSpeedPoly(d, t1)
