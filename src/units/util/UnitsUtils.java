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
        DIMENSIONLESS = createInternalUnit("Dimensionless", 0, dimensionlessMap);

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

    public static AnnotationMirror createInternalUnit(String originalName, int prefixExponent,
            Map<String, Integer> exponents) {
        AnnotationBuilder builder = new AnnotationBuilder(processingEnv, UnitsInternal.class);

        List<Integer> expos = new ArrayList<>();
        for (String key : exponents.keySet()) {
            expos.add(exponents.get(key));
        }

        builder.setValue("originalName", originalName);
        builder.setValue("prefixExponent", prefixExponent);
        builder.setValue("exponents", expos.toArray(new Integer[] {}));
        AnnotationMirror result = builder.build();

        return result;
    }
    
    public static String slotName(int slotID, String component) {
        return slotID + " " + component;
    }
    
    private static Set<String> baseUnits;
    
    public static Set<String> baseUnits() {
        if(baseUnits == null) {
            baseUnits = new TreeSet<>();
            baseUnits.add("m");
            baseUnits.add("s");
        }
        return baseUnits;
    }
}
