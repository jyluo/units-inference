import units.qual.UnitsRep;
import units.qual.Dimensionless;
import units.qual.m;
import units.qual.s;
import units.qual.UnitsBottom;
import units.UnitsTools;
import units.qual.*;

@Dimensionless
class Variables {

    // primitive fields
    @UnknownUnits int puf = ((@Dimensionless int) (10));
    @Dimensionless int pdf = ((@Dimensionless int) (30));

    // :: fixable-error: (assignment.type.incompatible)
    @m int pmf = ((@m int) (10));
    // :: fixable-error: (assignment.type.incompatible)
    @s int psf = ((@s int) (20));

    void primitiveVars(@Dimensionless Variables this) {
        @UnknownUnits int puv = ((@Dimensionless int) (10));
        @Dimensionless int pdv = ((@Dimensionless int) (30));

        // :: fixable-error: (assignment.type.incompatible)
        @m int pmv = ((@m int) (10));
        // :: fixable-error: (assignment.type.incompatible)
        @s int psv = ((@s int) (20));
    }

    // boxed number fields
    @UnknownUnits Integer buf = ((@Dimensionless int) (10));
    @Dimensionless Integer bdf = ((@Dimensionless int) (20));
    @UnitsBottom Integer bbf = null;
    // :: fixable-error: (assignment.type.incompatible)
    @m Integer bmf = ((@m int) (10));
    // :: fixable-error: (assignment.type.incompatible)
    @s Integer bsf = ((@s int) (20));

    void boxedNumberVars(@Dimensionless Variables this) {
        @UnknownUnits Integer buv = ((@Dimensionless int) (10));
        @Dimensionless Integer bdv = ((@Dimensionless int) (20));
        @UnitsBottom Integer bbv = ((@UnitsBottom Object) (null));
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer bmv = ((@m int) (10));
        // :: fixable-error: (assignment.type.incompatible)
        @s Integer bsv = ((@s int) (20));
    }

    void boxedConstructorCalls(@Dimensionless Variables this) {
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer implicitValueOfCall = ((@m int) (10));
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer explicitValueOfCall = ((@m Integer) (Integer.valueOf(((@m int) (10)))));
        // :: fixable-error: (constructor.invocation.invalid)
        @m Integer omittingConstructorArgType = ((@Dimensionless Integer) (new @m Integer(((@Dimensionless int) (10)))));
        @m Integer omittingConstructorReturnType = ((@Dimensionless Integer) (new @m Integer(((@UnitsRep(top=false, bot=false, prefixExponent=0, baseUnitComponents={@units.qual.BUC(unit="deg", exponent=0), @units.qual.BUC(unit="m", exponent=-1), @units.qual.BUC(unit="rad", exponent=0), @units.qual.BUC(unit="s", exponent=0)}) int) (10)) * UnitsTools.m)));
        // :: fixable-error: (assignment.type.incompatible)
        @m Integer omittingConstructorArgAndReturnType = ((@Dimensionless Integer) (new @m Integer(((@Dimensionless int) (10)))));
    }

    void boxedMethodCalls(@Dimensionless Variables this) {
        // :: fixable-error: (assignment.type.incompatible)
        @m Long staticPolyUnitMethod = ((@m long) (Integer.toUnsignedLong(((@m int) (10)))));
    }

    void customUnitForInsertion(@Dimensionless Variables this) {
        @UnitsRep(
                top = false,
                bot = false,
                prefixExponent = 4,
                baseUnitComponents = {
                    @BUC(unit = "m", exponent = 12),
                    @BUC(unit = "s", exponent = -34)
                })
        // :: fixable-error: (assignment.type.incompatible)
        Integer x = ((@UnitsRep(top=false, bot=false, prefixExponent=4, baseUnitComponents={@units.qual.BUC(unit="deg", exponent=0), @units.qual.BUC(unit="m", exponent=12), @units.qual.BUC(unit="rad", exponent=0), @units.qual.BUC(unit="s", exponent=-34)}) int) (50));
    }
}
