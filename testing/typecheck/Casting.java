import units.qual.*;

class Casting {
    @Dimensionless float dim;
    @UnknownUnits float top;
    @UnitsBottom float bot;
    @m float m;
    @s float s;

    // casting from dimensionless to anything is allowed
    void fromDimensionless() {
        @m int primM = (@m int) dim;
        @s Float boxS = (@s Float) dim;

        @Dimensionless int primDim = (@Dimensionless int) dim;
        @Dimensionless Float boxDim = (@Dimensionless Float) dim;

        // casting to unknownunits is unnecessary but allowed
        @UnknownUnits int boxTop = (@UnknownUnits int) dim;

        @UnitsBottom int boxBot = (@UnitsBottom int) dim;
    }

    // casting from unknownunits forbidden except to unknownunits
    void fromTop() {
        // :: warning: (cast.unsafe)
        @m int primM = (@m int) top;
        // :: warning: (cast.unsafe)
        @s Float boxS = (@s Float) top;

        // casting to dimensionless is forbidden
        // :: warning: (cast.unsafe)
        @Dimensionless int primDim = (@Dimensionless int) top;
        // :: warning: (cast.unsafe)
        @Dimensionless Float boxDim = (@Dimensionless Float) top;

        // casting to unknownunits is unnecessary but allowed
        @UnknownUnits int boxTop = (@UnknownUnits int) top;

        // casting to bottom is forbidden
        // :: warning: (cast.unsafe)
        @UnitsBottom int boxBot = (@UnitsBottom int) top;
    }

    // casting from bottom is unnecessary but allowed
    void fromBot() {
        @m int primM = (@m int) bot;
        @m Float boxM = (@m Float) bot;

        @Dimensionless int primDim = (@Dimensionless int) bot;
        @Dimensionless Float boxDim = (@Dimensionless Float) bot;

        @UnknownUnits int boxTop = (@UnknownUnits int) bot;
        @UnitsBottom int boxBot = (@UnitsBottom int) bot;
    }

    void fromUnit() {
        // casting to same unit is unnecessary but allowed
        @m int primM = (@m int) m;
        @s Float boxS = (@s Float) s;

        // casting to different unit is forbidden
        // :: warning: (cast.unsafe)
        primM = (@m int) s;
        // :: warning: (cast.unsafe)
        boxS = (@s float) m;

        // casting to dimensionless forbidden
        // :: warning: (cast.unsafe)
        @Dimensionless int primDim = (@Dimensionless int) m;
        // :: warning: (cast.unsafe)
        @Dimensionless Float boxDim = (@Dimensionless Float) s;

        // casting to unknownunits is unnecessary but allowed
        @UnknownUnits int boxTop = (@UnknownUnits int) m;
        boxTop = (@UnknownUnits int) s;

        // casting to bottom is forbidden
        // :: warning: (cast.unsafe)
        @UnitsBottom int boxBot = (@UnitsBottom int) m;
        // :: warning: (cast.unsafe)
        boxBot = (@UnitsBottom int) s;
    }
}
