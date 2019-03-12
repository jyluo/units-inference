import org.checkerframework.framework.qual.PolyAll;
import units.UnitsTools;
import units.qual.*;

// a class that cannot be instantiated with any units
class NoAnnotClass {}

@Dimensionless
class DimensionlessClass {}

// a class that can be instantiated with units
@UnknownUnits class UUClass {
    @PolyAll int polyAllMethod(@PolyAll UUClass this, @PolyAll int x) {
        return x;
    }

    @PolyAll int polyAllMethod2(@PolyAll UUClass this) {
        return 0;
    }
}

@PolyAll class PAClass {
    @PolyAll PAClass(@PolyAll int x) {}
}

@PolyUnit class PUClass {
    @PolyUnit PUClass(@PolyUnit int x) {}
}

@m class MeterClass {
    @m MeterClass() {}
}

class Constructors {
    void nonPolyConstructorTest() {
        @Dimensionless NoAnnotClass na1 = new NoAnnotClass();
        NoAnnotClass na2 = new NoAnnotClass();
        // can't use units annotation on a class with default type of Dimensionless
        // :: error: (constructor.invocation.invalid)
        @m NoAnnotClass na3 = new @m NoAnnotClass();
        // :: error: (assignment.type.incompatible)
        @m NoAnnotClass na4 = new NoAnnotClass();
        // :: error: (constructor.invocation.invalid)
        NoAnnotClass na5 = new @m NoAnnotClass();

        @Dimensionless DimensionlessClass d1 = new DimensionlessClass();
        DimensionlessClass d2 = new DimensionlessClass();
        // can't use units annotation on a class with declared type of Dimensionless
        // :: error: (constructor.invocation.invalid)
        @m DimensionlessClass d3 = new @m DimensionlessClass();
        // :: error: (assignment.type.incompatible)
        @m DimensionlessClass d4 = new DimensionlessClass();
        // :: error: (constructor.invocation.invalid)
        // :: error: (assignment.type.incompatible)
        DimensionlessClass d5 = new @m DimensionlessClass();

        @m UUClass uu1 = new @m UUClass();
        @s UUClass uu2 = new @s UUClass();
        // :: error: (assignment.type.incompatible)
        @s UUClass uu3 = new @m UUClass();

        @m MeterClass mc1 = new MeterClass();
        @m MeterClass mc2 = new @m MeterClass();
        // can't use a non-meter unit on a class with declared type of meters
        // :: error: (type.invalid.annotations.on.use)
        @m MeterClass mc3 = new @s MeterClass();
    }

    void polyAllConstructorTest() {
        // explicitly create a meter object
        @m PAClass pac1 = new @m PAClass(5 * UnitsTools.m);
        // also check the equivalent cast semantics
        pac1 = (@m PAClass) new PAClass(5 * UnitsTools.m);

        // create a meter object via @PolyAll
        @m PAClass pac2 = new PAClass(5 * UnitsTools.m);

        // creates a Dimensionless object via @PolyAll
        // :: error: (assignment.type.incompatible)
        @m PAClass pac3 = new PAClass(5);

        // warning issued for casting the Dimensionless object to seconds
        // :: warning: (cast.unsafe.constructor.invocation)
        @s PAClass pac4 = new @s PAClass(5);
        pac4 = (@s PAClass) new PAClass(5);

        // warning issued for casting the seconds object to meters
        // :: warning: (cast.unsafe.constructor.invocation)
        @m PAClass pac5 = new @m PAClass(5 * UnitsTools.s);
    }

    void polyAllReceiverTest() {
        @m int parc1 = (new @m UUClass()).polyAllMethod(5 * UnitsTools.m);

        // :: error: (assignment.type.incompatible)
        @m int parc2 = (new @s UUClass()).polyAllMethod(5 * UnitsTools.m);

        @m int parc3 = (new @m UUClass()).polyAllMethod2();

        // :: error: (assignment.type.incompatible)
        @m int parc4 = (new @s UUClass()).polyAllMethod2();
    }

    void polyUnitConstructorTest() {
        // explicitly create a meter object
        @m PUClass puc1 = new @m PUClass(5 * UnitsTools.m);
        // also check the equivalent cast semantics
        puc1 = (@m PUClass) new PUClass(5 * UnitsTools.m);

        // create a meter object via @PolyUnit
        @m PUClass puc2 = new PUClass(5 * UnitsTools.m);

        // creates a Dimensionless object via @PolyUnit
        // :: error: (assignment.type.incompatible)
        @m PUClass puc3 = new PUClass(5);

        // warning issued for casting the Dimensionless object to seconds
        // :: warning: (cast.unsafe.constructor.invocation)
        @s PUClass puc4 = new @s PUClass(5);
        puc4 = (@s PUClass) new PUClass(5);

        // warning issued for casting the seconds object to meters
        // :: warning: (cast.unsafe.constructor.invocation)
        @m PUClass puc5 = new @m PUClass(5 * UnitsTools.s);
    }
}
