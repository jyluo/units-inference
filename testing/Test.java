import units.qual.*;

class Main {
    public Main() {
        @UnitsInternal(originalName = "test", prefixExponent = 1, exponents = {
            @BaseUnitExpo(baseUnit= "m", exponent = 1)
        }) int x;

        x = 5 + 6;
    }
}