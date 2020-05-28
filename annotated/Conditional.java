import units.qual.Dimensionless;
import units.qual.*;

@Dimensionless
class Conditional<@Dimensionless T extends @Dimensionless RealFieldElement<@Dimensionless T>> {
    public Conditional() {}

    public @Dimensionless Conditional<T> compose(@Dimensionless Conditional<@Dimensionless T> this, final @Dimensionless boolean convention) {
        return convention ? composeInternal() : applyTo();
    }

    private @Dimensionless Conditional<T> composeInternal(@Dimensionless Conditional<@Dimensionless T> this) {
        return new @Dimensionless Conditional<>();
    }

    private <@Dimensionless T extends @Dimensionless RealFieldElement<@Dimensionless T>> @Dimensionless Conditional<T> applyTo(@Dimensionless Conditional<@Dimensionless T> this) {
        return new @Dimensionless Conditional<>();
    }
}
