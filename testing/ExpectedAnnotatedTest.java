import units.qual.UnknownUnits;
import units.qual.UnitsInternal;
import units.qual.*;

class Main {
    public Main() {
        // @m
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "m", exponent = 1)
        }) Integer x = ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=1),@BaseUnit(unit="s", exponent=0)}) int) (5)) + ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=1),@BaseUnit(unit="s", exponent=0)}) int) (6));

        x = ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=1),@BaseUnit(unit="s", exponent=0)}) int) (7)) - ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=1),@BaseUnit(unit="s", exponent=0)}) int) (8));

        x = ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=1),@BaseUnit(unit="s", exponent=0)}) int) (1)) * ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=0),@BaseUnit(unit="s", exponent=0)}) int) (2));

        x = ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=1),@BaseUnit(unit="s", exponent=0)}) int) (12)) / ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=0),@BaseUnit(unit="s", exponent=0)}) int) (5));

        // x = 40 % 9;

        // @s
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "s", exponent = 1)
        }) Integer y = ((@UnitsInternal(unknownUnits=false, unitsBottom=false, prefixExponent=0, baseUnits={@BaseUnit(unit="m", exponent=0),@BaseUnit(unit="s", exponent=1)}) int) (90));

        // @mPERs
        @UnknownUnits
        Integer z = x / y;

        z = x % x;

        // Integer y = x;

        // @m Integer x = 5 + 6;

        // Integer y = 9 - 10 - 11;
    }
}