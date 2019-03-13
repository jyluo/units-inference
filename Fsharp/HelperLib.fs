namespace UnitsTypeSystem

// helper module defining two versions of the same division calculation, where one is polymorphic over units
module HelperLib =
    let calcSpeed(dist, time) = dist / time
    let calcSpeedPoly (dist:int<_>, time:int<_>) = dist / time

    [<Measure>] type km
    [<Measure>] type h
    [<Measure>] type s

    // constants for testing type system
    let d = 30<km>
    let t1 = 10<h>
    let t2 = 10<s>
    let e = 10<1>   // same as dimensionless int by itself

    // also call the methods locally
    let hls1 = calcSpeed(d, t1) // if called, calcSpeed is bound to the type of d and t1, causing compile error in Program.fs
    // let hls2 = calcSpeedPoly(d, t1)
