import units.qual.*;
import units.UnitsTools;

class Variables {

    // primitive fields
    @UnknownUnits int puf = 10;
    @Dimensionless int pdf = 30;

    // :: fixable-error: (assignment.type.incompatible)
    @m int pmf = 10;
    // :: fixable-error: (assignment.type.incompatible)
    @s int psf = 20;

    void primitiveVars() {
        @UnknownUnits int puv = 10;
        @Dimensionless int pdv = 30;

        // :: fixable-error: (assignment.type.incompatible)
        @m int pmv = 10;
        // :: fixable-error: (assignment.type.incompatible)
        @s int psv = 20;
    }

    // boxed number fields
    @UnknownUnits Integer buf = 10;
    @Dimensionless Integer bdf = 20;
    @UnitsBottom Integer bbf = null;
    // :: fixable-error: (assignment.type.incompatible)
    @m Integer bmf = 10;
    // :: fixable-error: (assignment.type.incompatible)
    @s Integer bsf = 20;

    void boxedNumberVars() {
        @UnknownUnits Integer buv = 10;
        @Dimensionless Integer bdv = 20;
        @UnitsBottom Integer bbv = null;
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer bmv = 10;
        // :: fixable-error: (assignment.type.incompatible)
        @s Integer bsv = 20;
    }

    void boxedConstructorCalls() {
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer implicitValueOfCall = 10;
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer explicitValueOfCall = Integer.valueOf(10);
        // :: fixable-error: (constructor.invocation.invalid)
        @m Integer omittingConstructorArgType = new @m Integer(10);
        // :: fixable-error: (assignment.type.incompatible) :: fixable-error: (constructor.invocation.invalid)
        @m Integer omittingConstructorReturnType = new Integer(10 * UnitsTools.m);
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer omittingConstructorArgAndReturnType = new Integer(10);
    }

    void boxedMethodCalls() {
        // :: fixable-error: (assignment.type.incompatible)
        @m Long staticPolyUnitMethod = Integer.toUnsignedLong(10);
    }
}