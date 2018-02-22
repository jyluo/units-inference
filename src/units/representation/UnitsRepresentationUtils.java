package units.representation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.util.Elements;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ErrorReporter;
import units.qual.BaseUnit;
import units.qual.PolyUnit;
import units.qual.UnitsInternal;
import units.qual.m;
import units.qual.s;

/**
 * Utility class containing logic for creating and converting internal representations of units
 * between its 3 primary forms: {@link UnitsInternal} as annotation mirrors and
 * {@link TypecheckUnit}.
 *
 * TODO: {@code @Unit}, and alias forms.
 */
public class UnitsRepresentationUtils {
    private static UnitsRepresentationUtils singletonInstance;
    private static ProcessingEnvironment processingEnv;
    private static Elements elements;

    public AnnotationMirror POLYUNIT;

    // instances of {@link UnitsInternal} with values to represent UnknownUnits and UnitsBottom
    public AnnotationMirror UNKNOWNUNITS;
    public AnnotationMirror BOTTOM;

    // an instance of {@link UnitsInternal} with default values in its elements, which represents
    // dimensionless
    public AnnotationMirror DIMENSIONLESS;

    // an instance of {@link UnitsInternal} with no values in its elements
    public AnnotationMirror RAWUNITSINTERNAL;

    public AnnotationMirror METER;
    public AnnotationMirror SECOND;

    private UnitsRepresentationUtils(ProcessingEnvironment processingEnv, Elements elements) {
        UnitsRepresentationUtils.processingEnv = processingEnv;
        UnitsRepresentationUtils.elements = elements;
    }

    // postInit() is called after performing annotation loading to obtain the full list of base
    // units
    public void postInit() {
        POLYUNIT = AnnotationBuilder.fromClass(elements, PolyUnit.class);

        Map<String, Integer> zeroBaseDimensions = new TreeMap<>();
        for (String baseUnit : baseUnits()) {
            zeroBaseDimensions.put(baseUnit, 0);
        }
        // zeroBaseDimensions.put("s", 0);
        // zeroBaseDimensions.put("m", 0);

        UNKNOWNUNITS = createInternalUnit("UnknownUnits", true, false, 0, zeroBaseDimensions);
        BOTTOM = createInternalUnit("UnitsBottom", false, true, 0, zeroBaseDimensions);

        DIMENSIONLESS = createInternalUnit("Dimensionless", false, false, 0, zeroBaseDimensions);

        RAWUNITSINTERNAL = AnnotationBuilder.fromClass(elements, UnitsInternal.class);

        METER = AnnotationBuilder.fromClass(elements, m.class);
        SECOND = AnnotationBuilder.fromClass(elements, s.class);
    }

    public static UnitsRepresentationUtils getInstance(ProcessingEnvironment processingEnv,
            Elements elements) {
        if (singletonInstance == null) {
            singletonInstance = new UnitsRepresentationUtils(processingEnv, elements);
        }
        return singletonInstance;
    }

    public static UnitsRepresentationUtils getInstance() {
        if (singletonInstance == null) {
            ErrorReporter.errorAbort(
                    "getInstance() called without initializing UnitsRepresentationUtils.");
        }
        return singletonInstance;
    }

    private final Set<String> baseUnits = new TreeSet<>();

    public void addBaseUnit(String baseUnit) {
        baseUnits.add(baseUnit);
    }

    public Set<String> baseUnits() {
        return baseUnits;
    }

    // contains all supported units annotations, including aliases
    private final Set<AnnotationMirror> unitsAnnotations = new HashSet<>();

    public void addUnitsAnnotation(AnnotationMirror anno) {
        unitsAnnotations.add(anno);
    }

    public boolean isUnitsAnnotation(BaseAnnotatedTypeFactory realTypeFactory,
            AnnotationMirror anno) {
        return unitsAnnotations.contains(anno) || realTypeFactory.isSupportedQualifier(anno);
    }

    // A 1 to 1 mapping between an annotation mirror and its unique typecheck unit.
    private final Map<AnnotationMirror, TypecheckUnit> typecheckUnitCache = new HashMap<>();

    public TypecheckUnit createTypecheckUnit(AnnotationMirror anno) {
        if (!typecheckUnitCache.containsKey(anno)) {
            TypecheckUnit unit = new TypecheckUnit();

            if (AnnotationUtils.areSameByClass(anno, UnitsInternal.class)) {
                unit.setOriginalName(
                        AnnotationUtils.getElementValue(anno, "originalName", String.class, true));
                unit.setUnknownUnits(
                        AnnotationUtils.getElementValue(anno, "unknownUnits", Boolean.class, true));
                unit.setUnitsBottom(
                        AnnotationUtils.getElementValue(anno, "unitsBottom", Boolean.class, true));
                unit.setPrefixExponent(AnnotationUtils.getElementValue(anno, "prefixExponent",
                        Integer.class, true));

                Map<String, Integer> exponents = new HashMap<>();
                // default all base units to exponent 0
                for (String bu : baseUnits()) {
                    exponents.put(bu, 0);
                }
                for (AnnotationMirror bu : AnnotationUtils.getElementValueArray(anno, "baseUnits",
                        AnnotationMirror.class, true)) {
                    exponents.put(AnnotationUtils.getElementValue(bu, "unit", String.class, false),
                            AnnotationUtils.getElementValue(bu, "exponent", Integer.class, false));
                }

                for (String bu : exponents.keySet()) {
                    unit.setExponent(bu, exponents.get(bu));
                }
            } else {
                // not a units annotation
                return null;
            }
            typecheckUnitCache.put(anno, unit);
        }
        return typecheckUnitCache.get(anno);
    }

    public AnnotationMirror createInternalUnit(TypecheckUnit unit) {
        // see if cache already has a mapping, if so return from cache
        for (Entry<AnnotationMirror, TypecheckUnit> entry : typecheckUnitCache.entrySet()) {
            if (unit.equals(entry.getValue())) {
                return entry.getKey();
            }
        }

        // otherwise create an internal unit for the typecheck unit and add to cache
        AnnotationMirror anno = createInternalUnit(unit.getOriginalName(), unit.isUnknownUnits(),
                unit.isUnitsBottom(), unit.getPrefixExponent(), unit.getExponents());

        typecheckUnitCache.put(anno, unit);
        return anno;
    }

    public AnnotationMirror createInternalUnit(String originalName, boolean unknownUnits,
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
        // builder.setValue("originalName", originalName); // TODO: set original name
        builder.setValue("unknownUnits", unknownUnits);
        builder.setValue("unitsBottom", unitsBottom);
        builder.setValue("prefixExponent", prefixExponent);
        builder.setValue("baseUnits", expos);
        AnnotationMirror result = builder.build();

        return result;
    }
}
