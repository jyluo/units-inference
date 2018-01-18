import units.qual.*;

class Main {
    public Main() {
        // @m
        // @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
        //     @BaseUnit(unit = "m", exponent = 1)
        // }) Integer x = 10;

        // @ms
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = -3, baseUnits = {
            @BaseUnit(unit = "s", exponent = 1)
        }) Integer x = 10;

        // x = 7 - 8;

        // x = 1 * 2;

        // x = 12 / 5;

        // x = 40 % 9;

        // @s
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "s", exponent = 1)
        }) Integer y = 90;

        // // @mPERs
        Integer z = x / y;

        @UnitsBottom Integer g = 10;

        z = g;

        // @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = -3, baseUnits = {
        //     @BaseUnit(unit = "s", exponent = 1)
        // })
        float ms = toInferMethod(System.currentTimeMillis());
        // ms = toInferMethod(myTimeMillis());

        String word = null;
        if(false) {
            word = "stuff";
        }
    }

    @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = -3, baseUnits = {
            @BaseUnit(unit = "s", exponent = 1)
    }) long myTimeMillis() {
        return 10;
    }

    float toInferMethod(float input) {
        return input * Math.signum(input);
    }


    private float r;
    private float i;

    public String jblas_complexfloat(){
        if (i >= 0) {
          return r + " + " + i + "i";
        } else {
          return r + " - " + (-i) + "i";
        }
    }

    class Inner {
        public Inner(){}
    }

    public void testClasses(){
        String x = "test";
        Inner y = new Inner();
    }

}