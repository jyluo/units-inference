import units.qual.*;

class MathMethods {

    @m int m1, m2;
    @km int km1, km2;
    @rad double r1, r2;
    @deg double d1, d2;

    void testTrig() {
        @Dimensionless double x = Math.sin(r1);
        @Dimensionless double y = Math.cos(r1);
        @Dimensionless double z = Math.tan(r1);

        // :: error: (argument.type.incompatible)
        x = Math.sin(d1);
        // :: error: (argument.type.incompatible)
        y = Math.cos(d1);
        // :: error: (argument.type.incompatible)
        z = Math.tan(d1);

        r2 = Math.asin(x);
        r2 = Math.acos(y);
        r2 = Math.atan(z);
        r2 = Math.atan2(x, y);

        // :: error: (assignment.type.incompatible)
        d2 = Math.asin(x);
        // :: error: (assignment.type.incompatible)
        d2 = Math.acos(y);
        // :: error: (assignment.type.incompatible)
        d2 = Math.atan(z);
        // :: error: (assignment.type.incompatible)
        d2 = Math.atan2(x, y);

        // :: error: (units.differ)
        r2 = Math.atan2(r1, d1);

        x = Math.sinh(r1);
        y = Math.cosh(r1);
        z = Math.tanh(r1);

        // :: error: (argument.type.incompatible)
        x = Math.sinh(d1);
        // :: error: (argument.type.incompatible)
        y = Math.cosh(d1);
        // :: error: (argument.type.incompatible)
        z = Math.tanh(d1);

        d1 = Math.toDegrees(r1);
        r2 = Math.toRadians(d2);

        // :: error: (argument.type.incompatible)
        d1 = Math.toDegrees(d2);
        // :: error: (argument.type.incompatible)
        r2 = Math.toRadians(r1);

        // :: error: (assignment.type.incompatible)
        r2 = Math.toDegrees(r1);
        // :: error: (assignment.type.incompatible)
        d1 = Math.toRadians(d2);

        d2 = Math.hypot(d1, d2);

        // :: error: (assignment.type.incompatible)
        r1 = Math.hypot(d1, d2);
        // :: error: (assignment.type.incompatible) :: error: (units.differ)
        d2 = Math.hypot(r1, d2);
        // :: error: (units.differ)
        d2 = Math.hypot(d1, r1);
    }

    @m int im1, im2;
    @s long ls1, ls2;
    @g float fg1, fg2;
    @K double dk1, dk2;

    void testAbs() {
        im1 = Math.abs(im2);
        ls1 = Math.abs(ls2);
        fg1 = Math.abs(fg2);
        dk1 = Math.abs(dk2);

        // :: error: (assignment.type.incompatible)
        ls1 = Math.abs(im2);
        // :: error: (assignment.type.incompatible)
        fg1 = Math.abs(ls2);
        // :: error: (assignment.type.incompatible)
        dk1 = Math.abs(fg2);
        // :: error: (assignment.type.incompatible)
        im1 = (int) Math.abs(dk2);
    }

    void testExact() {
        im1 = Math.incrementExact(im2);
        ls1 = Math.incrementExact(ls2);

        // :: error: (assignment.type.incompatible)
        ls1 = Math.incrementExact(im2);
        // :: error: (assignment.type.incompatible)
        fg1 = Math.incrementExact(ls2);

        im1 = Math.decrementExact(im2);
        ls1 = Math.decrementExact(ls2);

        // :: error: (assignment.type.incompatible)
        ls1 = Math.decrementExact(im2);
        // :: error: (assignment.type.incompatible)
        fg1 = Math.decrementExact(ls2);

        im1 = Math.negateExact(im2);
        ls1 = Math.negateExact(ls2);

        // :: error: (assignment.type.incompatible)
        ls1 = Math.negateExact(im2);
        // :: error: (assignment.type.incompatible)
        fg1 = Math.negateExact(ls2);
    }

    @h long h1;
    @s int s1;
    @kmPERh int kmph;

    void testSame() {
        km1 = (int) Math.IEEEremainder(km2, h1);

        // :: error: (assignment.type.incompatible)
        kmph = (int) Math.IEEEremainder(km2, h1);

        m1 = Math.floorMod(m1, s1);

        km1 = (int) Math.floorMod(km2, h1);

        dk1 = Math.ceil(dk2);
        // :: error: (assignment.type.incompatible)
        dk1 = Math.ceil(fg1);

        dk1 = Math.floor(dk1);
        // :: error: (assignment.type.incompatible)
        dk1 = Math.floor(fg1);

        dk1 = Math.copySign(dk2, m1);
        // :: error: (assignment.type.incompatible)
        fg1 = (float) Math.copySign(dk2, m1);

        fg1 = Math.copySign(fg2, m1);
        // :: error: (assignment.type.incompatible)
        dk2 = Math.copySign(fg2, m1);

        dk1 = Math.nextAfter(dk2, dk1);
        // :: error: (units.differ)
        dk1 = Math.nextAfter(dk2, m1);
        // :: error: (assignment.type.incompatible)
        fg1 = (float) Math.nextAfter(dk2, dk1);

        fg1 = Math.nextAfter(fg2, fg1);
        // :: error: (units.differ)
        fg1 = Math.nextAfter(fg2, m1);
        // :: error: (assignment.type.incompatible)
        dk2 = Math.nextAfter(fg2, fg1);

        dk1 = Math.nextUp(dk2);
        // :: error: (assignment.type.incompatible)
        fg1 = (float) Math.nextUp(dk2);

        fg1 = Math.nextUp(fg2);
        // :: error: (assignment.type.incompatible)
        dk2 = Math.nextUp(fg2);

        dk1 = Math.nextDown(dk2);
        // :: error: (assignment.type.incompatible)
        fg1 = (float) Math.nextDown(dk2);

        fg1 = Math.nextDown(fg2);
        // :: error: (assignment.type.incompatible)
        dk2 = Math.nextDown(fg2);

        dk1 = Math.rint(dk2);
        // :: error: (assignment.type.incompatible)
        fg1 = (float) Math.rint(dk2);

        dk1 = Math.round(dk2);
        // :: error: (assignment.type.incompatible)
        ls1 = Math.round(dk2);

        fg1 = Math.round(fg2);
        // :: error: (assignment.type.incompatible)
        im1 = Math.round(fg2);

        ls1 = Math.toIntExact(ls2);
        // :: error: (assignment.type.incompatible)
        im1 = Math.toIntExact(ls2);

        dk1 = Math.scalb(dk2, m1);
        // :: error: (assignment.type.incompatible)
        fg1 = (float) Math.scalb(dk2, m1);

        fg1 = Math.scalb(fg2, m1);
        // :: error: (assignment.type.incompatible)
        dk1 = Math.scalb(fg2, m1);

        dk1 = Math.ulp(dk2);
        // :: error: (assignment.type.incompatible)
        fg1 = (float) Math.ulp(dk2);

        fg1 = Math.ulp(fg2);
        // :: error: (assignment.type.incompatible)
        dk1 = Math.ulp(fg2);
    }

    void testRest() {
        @Dimensionless double x = Math.signum(dk1);
        // :: error: (assignment.type.incompatible)
        m2 = (int) Math.signum(dk1);

        x = Math.signum(fg1);
        // :: error: (assignment.type.incompatible)
        m2 = (int) Math.signum(fg1);

        @Dimensionless double d = Math.exp(10);
        // :: error: (assignment.type.incompatible)
        m2 = (int) Math.exp(10);

        d = Math.expm1(10);
        // :: error: (assignment.type.incompatible)
        m2 = (int) Math.expm1(10);

        @Dimensionless int i = Math.getExponent(dk1);
        // :: error: (assignment.type.incompatible)
        m2 = Math.getExponent(dk1);

        i = Math.getExponent(fg1);
        // :: error: (assignment.type.incompatible)
        m2 = Math.getExponent(fg1);

        d = Math.log(20);
        // :: error: (assignment.type.incompatible)
        m2 = (int) Math.log(10);

        d = Math.log10(20);
        // :: error: (assignment.type.incompatible)
        m2 = (int) Math.log10(10);

        d = Math.log1p(20);
        // :: error: (assignment.type.incompatible)
        m2 = (int) Math.log1p(10);
    }

    void testMinMax() {
        im1 = Math.max(im1, im2);
        ls1 = Math.max(ls1, ls2);
        fg1 = Math.max(fg1, fg2);
        dk1 = Math.max(dk1, dk2);

        im1 = Math.min(im1, im2);
        ls1 = Math.min(ls1, ls2);
        fg1 = Math.min(fg1, fg2);
        dk1 = Math.min(dk1, dk2);

        // :: error: (assignment.type.incompatible)
        ls1 = Math.max(im1, im2);
        // :: error: (assignment.type.incompatible)
        fg1 = Math.max(ls1, ls2);
        // :: error: (assignment.type.incompatible)
        dk1 = Math.max(fg1, fg2);
        // :: error: (assignment.type.incompatible)
        im1 = (int) Math.max(dk1, dk2);

        // :: error: (assignment.type.incompatible)
        ls1 = Math.min(im1, im2);
        // :: error: (assignment.type.incompatible)
        fg1 = Math.min(ls1, ls2);
        // :: error: (assignment.type.incompatible)
        dk1 = Math.min(fg1, fg2);
        // :: error: (assignment.type.incompatible)
        im1 = (int) Math.min(dk1, dk2);
    }
}
