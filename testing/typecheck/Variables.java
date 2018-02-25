import units.qual.*;
import units.UnitsTools;

class Variables {
    // :: error: (assignment.type.incompatible)
    @m Integer a = 10;
    // :: error: (assignment.type.incompatible)
    @s Integer b = 20;

    public void Main() {
        // :: error: (assignment.type.incompatible)
        @m int x = 10;
        // :: error: (assignment.type.incompatible)
        @s int y = 20;
    }
}