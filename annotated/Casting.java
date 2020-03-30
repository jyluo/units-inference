import units.qual.m;
import units.qual.Dimensionless;
import units.qual.*;

@Dimensionless
class Casting {
    //    // :: fixable-error: (assignment.type.incompatible)
    //    @m int primM2 = (int) 10.0f;
    //    // :: fixable-error: (assignment.type.incompatible)
    //    @s Integer primS = 30;
    //
    //    int primDim = (int) 20.0f;

    @m
    int boxDim = ((@m int) (20));
    @m int boxM = (@m int) boxDim;

    //    void cast() {
    //    	int x = 20;
    //    	@m int y = (@m int) x;
    //
    //    	Integer boxDim = 20;
    //        @m Integer boxM = (@m Integer) boxDim;
    //    }
}
