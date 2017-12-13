import units.qual.*;

class Main {
    public Main() {
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "m", exponent = 1),
            @BaseUnit(unit = "s", exponent = -3)
        }) Integer x = 5 + 6;

        x = 7 - 8;

        x = 1 * 2;

        // Integer y = x;

        // @m Integer x = 5 + 6;

        // Integer y = 9 - 10 - 11;
    }
}