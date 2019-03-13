open UnitsTypeSystem

module Main =
    // calling a function from another module, the parameter types are assumed to be dimensionless integers
    let s1 = HelperLib.calcSpeed(HelperLib.e, HelperLib.e)  // ok if local call in HelperLib is commented, compile time error if not commented
    let speedError = HelperLib.calcSpeed(HelperLib.d, HelperLib.t1) // compile time error if above is not commented

    // calling a function explicitly annotated as polymorphic is ok
    let s1Poly = HelperLib.calcSpeedPoly(HelperLib.d, HelperLib.t1)  // ok

    // lets also define a local copy of both methods found in HelperLib
    let localCalcSpeed (dist, time) = dist / time
    let localCalcSpeedPoly (dist:int<_>, time:int<_>) = dist / time

    // calling the local unannotated copy is ok, F# type inference infers the units of the function parameters and returns
    let s2 = localCalcSpeed(HelperLib.d, HelperLib.t1)

    let s2BadCall = localCalcSpeed(HelperLib.d, HelperLib.t2)   // error issued here, the type signature of localCalcSpeed is already unified iwth the call for variable s2, and cannot unify with this call

    // calling the local polymorphic annotated copy is also ok
    let lSpeedPoly = localCalcSpeedPoly(HelperLib.d, HelperLib.t1)
