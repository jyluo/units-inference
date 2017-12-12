import units.qual.*;

class Main {
    public Main() {
        @UnitsInternal(unknownUnits = true, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "m", exponent = 1),
            @BaseUnit(unit = "s", exponent = -3)
        }) Integer x = 5 + 6 + 7;

        // Integer y = x;

        // @m Integer x = 5 + 6;

        Integer y = 9 - 10 - 11;
    }
}