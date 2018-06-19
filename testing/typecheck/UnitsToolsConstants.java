import units.UnitsTools;
import units.qual.*;

class UnitsToolsConstants {

    @UnknownUnits Integer top;

    @UnknownUnits Integer uu;
    @UnitsBottom Integer bot;
    @Dimensionless Integer dim;
    @m Integer m;
    @s Integer s;
    @ms Integer ms;

    public void Main() {
        uu = UnitsTools.m;
        uu = UnitsTools.s;
        uu = UnitsTools.ms;
        uu = top;

        m = UnitsTools.m;
        // :: error: (assignment.type.incompatible)
        m = UnitsTools.s;
        // :: error: (assignment.type.incompatible)
        m = UnitsTools.ms;

        s = UnitsTools.s;
        // :: error: (assignment.type.incompatible)
        s = UnitsTools.m;
        // :: error: (assignment.type.incompatible)
        s = UnitsTools.ms;
    }

    public void TestingOnly() {
        uu = UnitsTools.top;
        bot = UnitsTools.bottom;
        dim = UnitsTools.dimensionless;
    }
}
