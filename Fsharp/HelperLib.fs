namespace UnitsTypeSystem

// helper module defining two versions of the same division calculation, where one is polymorphic over units
module HelperLib =
    let calcSpeed (dist:int, time:int) = dist / time
    let calcSpeedPoly (dist:int<_>, time:int<_>) = dist / time
