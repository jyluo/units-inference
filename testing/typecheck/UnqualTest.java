import units.qual.*;

class UnqualTest {
    // :: error: (assignment.type.incompatible)
    @kg int kg = 5;
    @kg int alsokg = kg;
}
