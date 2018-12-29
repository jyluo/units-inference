package units;

import units.qual.*;

@SuppressWarnings("units")
public class UnitsTools {
    // Static Constants
    public static final @m byte m = 1;
    public static final @km byte km = 1;

    public static final @s byte s = 1;
    public static final @ms byte ms = 1;
    public static final @us byte us = 1;
    public static final @ns byte ns = 1;

    public static final @rad byte rad = 1;
    public static final @deg byte deg = 1;

    // Testing use only
    public static final @UnknownUnits byte top = 1;
    public static final @UnitsBottom byte bottom = 1;
    public static final @Dimensionless byte dimensionless = 1;

    // Conversion Functions
    public static final @ms int secondsToMilliSeconds(@s int seconds) {
        return seconds * 1000;
    }
}
