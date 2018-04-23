package units;

import units.qual.*;

@SuppressWarnings("units")
public class UnitsTools {
    // Static Constants
    public static final @m int m = 1;
    public static final @s int s = 1;
    public static final @ms Integer ms = 1;
    public static final @ns Integer ns = 1;

    public static final @rad int rad = 1;
    public static final @deg int deg = 1;

    // Testing use only
    public static final @UnknownUnits int top = 1;
    public static final @UnitsBottom int bottom = 1;
    public static final @Dimensionless int dimensionless = 1;

    // Conversion Functions
    public static final @ms int secondsToMilliSeconds(@s int seconds) {
        return seconds * 1000;
    }
}
