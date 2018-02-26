import units.qual.*;
import org.checkerframework.framework.qual.PolyAll;

class Subtyping {

    @UnknownUnits Integer top;

    @UnknownUnits Integer uu;
    @UnitsBottom Integer bot;
    @Dimensionless Integer dim;
    @m Integer m;
    @s Integer s;

    public void Main() {
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

    @PolyAll Integer polyall;
    @PolyUnit Integer polyunit;
    @UnitsInternal Integer raw;

    public void OddCases(){
        // For directly testing the subtyping relations defined between poly and unit types
        // these are not expected to be in source code
        polyall = raw;
        raw = polyall;
        polyunit = raw;
        raw = polyunit;

        polyall = polyunit;
        polyunit = polyall;
        polyall = m;
        m = polyall;
    }
}
