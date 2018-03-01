import units.qual.*;

class Variables {

    @UnknownUnits Integer a = 10;

    @Dimensionless Integer b = 20;

    @UnitsBottom Integer c = null;

    // :: fixable-error: (assignment.type.incompatible)
    @m Integer d = 10;
    // :: fixable-error: (assignment.type.incompatible)
    @s Integer e = 20;

    public void Main() {
        @UnknownUnits int i = 10;
        @Dimensionless int j = 30;

        // :: fixable-error: (assignment.type.incompatible)
        @m int k = 10;
        // :: fixable-error: (assignment.type.incompatible)
        @s int l = 20;
    }
}