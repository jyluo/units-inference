import units.qual.*;

class Main {
    public Main() {
        // @m
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "m", exponent = 1)
        }) Integer x = 5 + 6;

        x = 7 - 8;

        x = 1 * 2;

        x = 12 / 5;

        // x = 40 % 9;

        // @s
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "s", exponent = 1)
        }) Integer y = 90;

        // @mPERs
        Integer z = x / y;

        z = x % x;

        z = x + y;

        z = x - y;

        // Integer y = x;

        // @m Integer x = 5 + 6;

        // Integer y = 9 - 10 - 11;
    }
}