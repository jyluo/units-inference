import units.qual.*;

class Main {
    public Main() {
        @UnitsInternal(prefixExponent = 0, exponents = {0, 0}) 
        Integer x = 5 + 6;

        Integer y = 5 - 6;
    }
}