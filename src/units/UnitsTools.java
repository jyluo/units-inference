package units;

import units.qual.*;

@SuppressWarnings("units")
public class UnitsTools {
    public static final @UnitsInternal(unknownUnits = false, unitsBottom = false,
            prefixExponent = 0, baseUnits = {@BaseUnit(unit = "m", exponent = 1)}) int m = 1;
    public static final @UnitsInternal(unknownUnits = false, unitsBottom = false,
            prefixExponent = 0, baseUnits = {@BaseUnit(unit = "s", exponent = 1)}) int s = 1;
    public static final @UnitsInternal(unknownUnits = false, unitsBottom = false,
            prefixExponent = -3, baseUnits = {@BaseUnit(unit = "s", exponent = 1)}) int ms = 1;

    // Testing use only
    public static final @UnknownUnits int top = 1;
    public static final @UnitsBottom int bottom = 1;
    public static final @Dimensionless int dimensionless = 1;

}
