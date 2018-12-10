import units.UnitsTools;
import units.qual.*;

class Casting {

    // casting from dimensionless allowed
    @m int fromDimToM = (@m int) 10;

    // :: fixable-error: (assignment.type.incompatible)
    @m int fromDimToM2 = (int) 10.0f;

    int remainDim = (int) 20.0f;

    // :: fixable-error: (assignment.type.incompatible)
    @s int fromDimToS = remainDim;

    // boxed tests

    Integer remainDimBox = 20;

    @m Integer fromDimToMBox = (@m Integer) remainDimBox;

    // casting from dimensionless to unknownunits is unnecessary but allowed
    @UnknownUnits int fromDimToTop = (@UnknownUnits int) 10;
}
