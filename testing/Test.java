import units.qual.*;
import units.UnitsTools;

class Main {
    // public void subtypeTest() {
    //     // Test 1:
    //     // @var <: @m
    //     Integer v1 = 5;

    //     @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
    //         @BaseUnit(unit = "m", exponent = 1)
    //     }) Integer m = v1;

    //     // Test 2:
    //     // @var <: @top
    //     Integer v2 = 5;

    //     @UnitsInternal(unknownUnits = true, unitsBottom = false, prefixExponent = 0, baseUnits = {})
    //     Integer top = v2;

    //     // Test 3:
    //     // @var <: @bottom
    //     Integer v3 = 5;

    //     @UnitsInternal(unknownUnits = false, unitsBottom = true, prefixExponent = 0, baseUnits = {})
    //     Integer bottom = v3;

    //     // Test 4:
    //     // @bottom <: @top
    //     top = bottom;

    //     // Test 5:
    //     // @bottom <: @var
    //     v1 = bottom;
    //     v2 = bottom;
    //     v3 = bottom;

    //     // Test 6: unsat tests, uncomment to run and see that there's 0 annotations
    //     // // @m <: @bottom
    //     // bottom = v1;
    //     // @top <: @bottom
    //     bottom = top;       // not working... why???
    // }
    @m Integer a = 10;
    @m Integer b = 20;

    public void typecheckTest(){
        a = b;   // this is okay in typecheck mode
    }

    public Main() {
        // @m
        @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = 0, baseUnits = {
            @BaseUnit(unit = "m", exponent = 1)
        }) Integer x = 10;

        @m Integer y = 20;
    }




    // @UnitsInternal(unknownUnits = false, unitsBottom = false, prefixExponent = -3, baseUnits = {
    //         @BaseUnit(unit = "s", exponent = 1)
    // }) long myTimeMillis() {
    //     return 10;
    // }

    // float toInferMethod(float input) {
    //     return input * Math.signum(input);
    //   // return Math.signum(input) * input;
    //   // return 10 * UnitsTools.m;
    // }

    // private float r;
    // private float i;

    // public String jblas_complexfloat(){
    //     if (i >= 0) {
    //       return r + " + " + i + "i";
    //     } else {
    //       return r + " - " + (-i) + "i";
    //     }
    // }

    // class Inner {
    //     public Inner(){}
    // }

    // public void testClasses(){
    //     String x = "test";
    //     Inner y = new Inner();
    // }

}