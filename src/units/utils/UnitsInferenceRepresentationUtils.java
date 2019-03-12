package units.utils;

import checkers.inference.model.ConstantSlot;
import checkers.inference.solver.util.Statistics;
import java.lang.annotation.Annotation;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.util.Elements;
import units.qual.Dimensionless;
import units.qual.UnitsBottom;
import units.qual.UnitsRep;
import units.qual.UnknownUnits;

/**
 * Utility class containing logic for creating, updating, and converting internal representations of
 * units between its 2 primary forms: {@link UnitsRep} as annotation mirrors and {@link
 * TypecheckUnit}. This version contains additional methods for inference use.
 */
public class UnitsInferenceRepresentationUtils extends UnitsRepresentationUtils {

    /**
     * A set of the surface units annotation classes added to the {@link #unitsAnnotationMirrorMap}.
     * This is used in Units Inference.
     */
    private final Set<Class<? extends Annotation>> surfaceUnitsSet = new HashSet<>();

    /** All base units actually used in the program, which should be serialized into z3 */
    private Set<String> serializeableBaseUnitNames;

    /** Whether to serialize the prefix exponent or not */
    private boolean serializePrefix;

    public UnitsInferenceRepresentationUtils(
            ProcessingEnvironment processingEnv, Elements elements) {
        super(processingEnv, elements);
    }

    @Override
    public void postInit(
            Set<Class<? extends Annotation>> loadedBaseUnits,
            Set<Class<? extends Annotation>> loadedAliasUnits) {
        super.postInit(loadedBaseUnits, loadedAliasUnits);
        surfaceUnitsSet.addAll(loadedBaseUnits);
        surfaceUnitsSet.addAll(loadedAliasUnits);
        surfaceUnitsSet.add(UnknownUnits.class);
        surfaceUnitsSet.add(UnitsBottom.class);
        surfaceUnitsSet.add(Dimensionless.class);
    }

    public void setSerializedBaseUnits(Set<ConstantSlot> constantSlots) {
        if (serializeableBaseUnitNames != null) {
            // this case occurs when re-running inference for unsat core, no need to set
            // units again
            return;
        }

        // tabulate whether there's any appearance of prefix != 0
        serializePrefix = false; // assumption

        // tabulate the number of appearance of base unit exponents != 0
        serializeableBaseUnitNames = new HashSet<>();

        for (ConstantSlot slot : constantSlots) {
            TypecheckUnit unit = createTypecheckUnit(slot.getValue());
            // System.err.println(unit);

            serializePrefix = serializePrefix || (unit.getPrefixExponent() != 0);

            for (Entry<String, Integer> baseUnitExponents : unit.getExponents().entrySet()) {
                String bu = baseUnitExponents.getKey();
                boolean exponentUsed = baseUnitExponents.getValue() != 0;
                if (exponentUsed) {
                    serializeableBaseUnitNames.add(bu);
                }
            }
        }

        Statistics.addOrIncrementEntry("serialize_prefix", serializePrefix() ? 1 : 0);
        Statistics.addOrIncrementEntry("serialize_baseunits", serializableBaseUnits().size());
    }

    public Set<String> serializableBaseUnits() {
        assert serializeableBaseUnitNames != null;
        return serializeableBaseUnitNames;
    }

    public boolean serializePrefix() {
        return serializePrefix;
    }

    public Set<Class<? extends Annotation>> surfaceUnitsSet() {
        return surfaceUnitsSet;
    }
}
