import units.qual.*;

class Main {
    public Main() {
        @UnitsInternal(originalName = "dummy", prefixExponent = 1, exponents = {1, 1}) 
        Integer x = 5 + 6;
    }
}