package units.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.util.Elements;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.ErrorReporter;
import org.checkerframework.javacutil.Pair;
import units.qual.BaseUnit;
import units.qual.PolyUnit;
import units.qual.UnitsBottom;
import units.qual.UnitsInternal;
import units.qual.UnknownUnits;
import units.qual.m;
import units.qual.s;

public class UnitsUtils {
    private static UnitsUtils singletonInstance;
    private static ProcessingEnvironment processingEnv;
    private static Elements elements;

    public static AnnotationMirror POLYUNIT;
    public static AnnotationMirror UNKNOWNUNITS;
    public static AnnotationMirror BOTTOM;
    public static AnnotationMirror DIMENSIONLESS;

    // an instance of {@link UnitsInternal} with no values in its elements
    public static AnnotationMirror RAWUNITSINTERNAL;

    public static AnnotationMirror METER;
    public static AnnotationMirror SECOND;

    private UnitsUtils(ProcessingEnvironment processingEnv, Elements elements) {
        UnitsUtils.processingEnv = processingEnv;
        UnitsUtils.elements = elements;

        POLYUNIT = AnnotationBuilder.fromClass(elements, PolyUnit.class);
        UNKNOWNUNITS = AnnotationBuilder.fromClass(elements, UnknownUnits.class);
        BOTTOM = AnnotationBuilder.fromClass(elements, UnitsBottom.class);

        // TODO: loop all base dimensions
        Map<String, Integer> dimensionlessMap = new TreeMap<>();
        dimensionlessMap.put("s", 0);
        dimensionlessMap.put("m", 0);
        DIMENSIONLESS = createInternalUnit("Dimensionless", false, false, 0, dimensionlessMap);

        RAWUNITSINTERNAL = AnnotationBuilder.fromClass(elements, UnitsInternal.class);

        METER = AnnotationBuilder.fromClass(elements, m.class);
        SECOND = AnnotationBuilder.fromClass(elements, s.class);
    }

    public static UnitsUtils getInstance(ProcessingEnvironment processingEnv, Elements elements) {
        if (singletonInstance == null) {
            singletonInstance = new UnitsUtils(processingEnv, elements);
        }
        return singletonInstance;
    }

    public static UnitsUtils getInstance() {
        if (singletonInstance == null) {
            ErrorReporter.errorAbort("getInstance() called without initializing UnitsUtils.");
        }
        return singletonInstance;
    }

    private static Set<String> baseUnits;

    public static Set<String> baseUnits() {
        if (baseUnits == null) {
            baseUnits = new TreeSet<>();
            // TODO: integrate with RealATF and add actual base units declared by user
            baseUnits.add("m");
            baseUnits.add("s");
        }
        return baseUnits;
    }

    public static AnnotationMirror createInternalUnit(String originalName, boolean unknownUnits,
            boolean unitsBottom, int prefixExponent, Map<String, Integer> exponents) {
        // not allowed to set both a UU and UB to true on the same annotation
        assert !(unknownUnits && unitsBottom);

        AnnotationBuilder builder = new AnnotationBuilder(processingEnv, UnitsInternal.class);

        List<AnnotationMirror> expos = new ArrayList<>();
        for (String key : exponents.keySet()) {
            // Construct BaseUnit annotations for each exponent
            AnnotationBuilder buBuilder = new AnnotationBuilder(processingEnv, BaseUnit.class);
            buBuilder.setValue("unit", key);
            buBuilder.setValue("exponent", exponents.get(key));
            expos.add(buBuilder.build());
        }

        // See {@link UnitsInternal}
        builder.setValue("originalName", originalName);
        builder.setValue("unknownUnits", unknownUnits);
        builder.setValue("unitsBottom", unitsBottom);
        builder.setValue("prefixExponent", prefixExponent);
        builder.setValue("baseUnits", expos);
        AnnotationMirror result = builder.build();

        return result;
    }

    // Encoder utilities ==========================================================================
    private static final char idComponentSeparator = '-';
    public static final String uuSlotName = "UnknownUnits";
    public static final String ubSlotName = "UnitsBottom";
    public static final String prefixSlotName = "Prefix";

    public static String z3VarName(int slotID, String component) {
        return slotID + String.valueOf(idComponentSeparator) + component;
    }

    public static Pair<Integer, String> slotFromZ3VarName(String z3VarName) {
        int dashIndex = z3VarName.indexOf(idComponentSeparator);

        int slotID;
        String component;

        if (dashIndex < 0) {
            slotID = Integer.valueOf(z3VarName);
            component = null;
        } else {
            slotID = Integer.valueOf(z3VarName.substring(0, dashIndex));
            component = z3VarName.substring(dashIndex + 1);
        }

        return Pair.of(slotID, component);
    }
}
