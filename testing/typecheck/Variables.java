import units.qual.*;

class Variables {

    @UnknownUnits Integer a = 10;
    // :: error: (assignment.type.incompatible)
    @UnitsBottom Integer b = 20;

    @Dimensionless Integer c = 30;

    // :: error: (assignment.type.incompatible)
    @m Integer d = 10;
    // :: error: (assignment.type.incompatible)
    @s Integer e = 20;

    public void Main() {
        @UnknownUnits int h = 10;
        // :: error: (assignment.type.incompatible)
        @UnitsBottom int i = 20;

        @Dimensionless int j = 30;

        // :: error: (assignment.type.incompatible)
        @m int k = 10;
        // :: error: (assignment.type.incompatible)
        @s int l = 20;
    }
}
