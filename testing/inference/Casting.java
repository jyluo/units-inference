import units.qual.*;

class Casting {
    // :: fixable-error: (assignment.type.incompatible)
    @m int primM2 = (int) 10.0f;
    // :: fixable-error: (assignment.type.incompatible)
    @s Integer primS = 30;

    int primDim = (int) 20.0f;

    Integer boxDim = 20;

    @m Integer boxM = (@m Integer) boxDim;
}
