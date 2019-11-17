import units.qual.*;

class Subtyping {

    @UnknownUnits Integer top;

    @UnknownUnits Integer uu;
    @UnitsBottom Integer bot;
    @Dimensionless Integer dim;
    @m Integer m;
    @s Integer s;

    void test() {
        uu = bot;
        uu = dim;
        uu = m;
        uu = top;

        // :: error: (assignment.type.incompatible)
        bot = uu;
        // :: error: (assignment.type.incompatible)
        bot = dim;
        // :: error: (assignment.type.incompatible)
        bot = m;

        // :: error: (assignment.type.incompatible)
        dim = uu;
        dim = bot;
        // :: error: (assignment.type.incompatible)
        dim = m;

        // :: error: (assignment.type.incompatible)
        m = uu;
        m = bot;
        // :: error: (assignment.type.incompatible)
        m = dim;
        // :: error: (assignment.type.incompatible)
        m = s;

        m = m;
        s = s;
    }
}
