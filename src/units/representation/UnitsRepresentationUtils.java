package units.representation;

import java.lang.annotation.Annotation;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.util.Elements;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.qual.PolyAll;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ErrorReporter;
import checkers.inference.qual.VarAnnot;
import units.qual.BaseUnit;
import units.qual.Dimensionless;
import units.qual.PolyUnit;
import units.qual.UnitsAlias;
import units.qual.UnitsBottom;
import units.qual.UnitsInternal;
import units.qual.UnknownUnits;

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

    /** An instance of {@link PolyAll} as an {@link AnnotationMirror} */
    public AnnotationMirror POLYALL;

    /** An instance of {@link PolyUnit} as an {@link AnnotationMirror} */
    public AnnotationMirror POLYUNIT;

    /** An instance of {@link UnitsInternal} with no values in its elements */
    public AnnotationMirror RAWUNITSINTERNAL;

    /** Instances of {@link UnitsInternal} with values to represent UnknownUnits and UnitsBottom */
    public AnnotationMirror TOP;
    public AnnotationMirror BOTTOM;

    /**
     * An instance of {@link UnitsInternal} with default values in its elements, which represents
     * dimensionless
     */
    public AnnotationMirror DIMENSIONLESS;

    /**
     * Instances of {@link UnknownUnits} and {@link UnitsBottom} for insertion to source;
     */
    public AnnotationMirror SURFACE_TOP;
    public AnnotationMirror SURFACE_BOTTOM;

    /**
     * Instance of {@link VarAnnot} for use in UnitsVisitor in infer mode.
     */
    public AnnotationMirror VARANNOT;

    // public AnnotationMirror METER;

    // Comparator used to sort annotation classes by their simple class name
    private static Comparator<Class<? extends Annotation>> annoClassComparator =
            new Comparator<Class<? extends Annotation>>() {
                @Override
                public int compare(Class<? extends Annotation> a1, Class<? extends Annotation> a2) {
                    return a1.getSimpleName().compareTo(a2.getSimpleName());
                }
            };

    /** The set of base units */
    private final Set<Class<? extends Annotation>> baseUnits = new TreeSet<>(annoClassComparator);
    private Set<String> baseUnitNames;

    /** The set of alias units defined as qualifiers */
    private final Set<Class<? extends Annotation>> aliasUnits = new TreeSet<>(annoClassComparator);

    /**
     * A map from surface units annotation mirrors to their internal units representation.
     */
    private final Map<AnnotationMirror, AnnotationMirror> unitsAnnotationMirrorMap =
            AnnotationUtils.createAnnotationMap();

    /**
     * An immutable view of {@link #unitsAnnotationMirrorMap}.
     */
    private final Map<AnnotationMirror, AnnotationMirror> immutableUnitsAnnotationMirrorMap;

    /**
     * A set of the surface units annotation classes added to the {@link #unitsAnnotationMirrorMap}.
     */
    private final Set<Class<? extends Annotation>> surfaceUnitsSet = new HashSet<>();

    /**
     * The unitsAnnotationMirrorMap with its keys and values swapped.
     */
    private final Map<AnnotationMirror, AnnotationMirror> swappedMap =
            AnnotationUtils.createAnnotationMap();
    /**
     * An immutable view of {@link #swappedMap}.
     */
    private Map<AnnotationMirror, AnnotationMirror> immutableSwappedMap;

    private UnitsRepresentationUtils(ProcessingEnvironment processingEnv, Elements elements) {
        UnitsRepresentationUtils.processingEnv = processingEnv;
        UnitsRepresentationUtils.elements = elements;

        immutableUnitsAnnotationMirrorMap = Collections.unmodifiableMap(unitsAnnotationMirrorMap);
        immutableSwappedMap = Collections.unmodifiableMap(swappedMap);
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

    public void addBaseUnit(Class<? extends Annotation> baseUnit) {
        baseUnits.add(baseUnit);
    }

    public Set<String> baseUnits() {
        // copy simple names of all base units into the set if it hasn't been done before
        if (baseUnitNames == null) {
            baseUnitNames = new TreeSet<>();
            for (Class<? extends Annotation> baseUnit : baseUnits) {
                baseUnitNames.add(baseUnit.getSimpleName());
            }

            baseUnitNames = Collections.unmodifiableSet(baseUnitNames);
        }

        return baseUnitNames;
    }

    public Set<Class<? extends Annotation>> surfaceUnitsSet() {
        return surfaceUnitsSet;
    }

    public void addAliasUnit(Class<? extends Annotation> aliasUnit) {
        aliasUnits.add(aliasUnit);
    }

    /**
     * Creates and returns an exponent values map with all defined base units sorted alphabetically
     * according to unit symbol name, and with the exponent values set to 0.
     */
    protected Map<String, Integer> createZeroFilledBaseUnitsMap() {
        Map<String, Integer> map = new TreeMap<>();
        for (String baseUnit : baseUnits()) {
            map.put(baseUnit, 0);
        }
        return map;
    }

    // public Set<Class<? extends Annotation>> aliasUnits() {
    // return aliasUnits;
    // }

    // postInit() is called after performing annotation loading to obtain the full list of base
    // units
    public void postInit() {
        POLYALL = AnnotationBuilder.fromClass(elements, PolyAll.class);
        POLYUNIT = AnnotationBuilder.fromClass(elements, PolyUnit.class);

        RAWUNITSINTERNAL = AnnotationBuilder.fromClass(elements, UnitsInternal.class);

        Map<String, Integer> zeroBaseDimensions = createZeroFilledBaseUnitsMap();
        TOP = createInternalUnit("UnknownUnits", true, false, 0, zeroBaseDimensions);
        BOTTOM = createInternalUnit("UnitsBottom", false, true, 0, zeroBaseDimensions);
        DIMENSIONLESS = createInternalUnit("Dimensionless", false, false, 0, zeroBaseDimensions);

        // Map<String, Integer> meterDimensions = createZeroFilledBaseUnitsMap();
        // meterDimensions.put("m", 1);
        // METER = createInternalUnit("Meter", false, false, 0, meterDimensions);

        unitsAnnotationMirrorMap.put(AnnotationBuilder.fromClass(elements, UnknownUnits.class),
                TOP);
        unitsAnnotationMirrorMap.put(AnnotationBuilder.fromClass(elements, UnitsBottom.class),
                BOTTOM);
        unitsAnnotationMirrorMap.put(AnnotationBuilder.fromClass(elements, Dimensionless.class),
                DIMENSIONLESS);

        surfaceUnitsSet.add(UnknownUnits.class);
        surfaceUnitsSet.add(UnitsBottom.class);
        surfaceUnitsSet.add(Dimensionless.class);

        for (Class<? extends Annotation> baseUnit : baseUnits) {
            createInternalBaseUnit(baseUnit);
        }
        surfaceUnitsSet.addAll(baseUnits);

        for (Class<? extends Annotation> aliasUnit : aliasUnits) {
            createInternalAliasUnit(aliasUnit);
        }
        surfaceUnitsSet.addAll(aliasUnits);

        SURFACE_TOP = AnnotationBuilder.fromClass(elements, UnknownUnits.class);
        SURFACE_BOTTOM = AnnotationBuilder.fromClass(elements, UnitsBottom.class);

        // for (Entry<AnnotationMirror, AnnotationMirror> entry : unitsAnnotationMirrorMap
        // .entrySet()) {
        // System.out.println(" == built map " + entry.getKey() + " --> " + entry.getValue());
        // }
    }

    /**
     * Creates an internal unit representation for the given base unit and adds it to the alias map.
     */
    private void createInternalBaseUnit(Class<? extends Annotation> baseUnitClass) {
        // check to see if the annotation has already been mapped before
        AnnotationMirror baseUnitAM = AnnotationBuilder.fromClass(elements, baseUnitClass);
        if (unitsAnnotationMirrorMap.containsKey(baseUnitAM)) {
            return;
        }

        Map<String, Integer> exponents = createZeroFilledBaseUnitsMap();

        // set the exponent of the given base unit to 1
        exponents.put(baseUnitClass.getSimpleName(), 1);
        // create the internal unit and add to alias map
        unitsAnnotationMirrorMap.put(baseUnitAM,
                createInternalUnit(baseUnitClass.getCanonicalName(), false, false, 0, exponents));
    }

    /**
     * Creates an internal unit representation for the given alias unit and adds it to the alias
     * map.
     */
    private void createInternalAliasUnit(Class<? extends Annotation> aliasUnitClass) {
        // check to see if the annotation has already been mapped before
        AnnotationMirror aliasUnitAM = AnnotationBuilder.fromClass(elements, aliasUnitClass);
        if (unitsAnnotationMirrorMap.containsKey(aliasUnitAM)) {
            return;
        }

        int prefix = 0;

        Map<String, Integer> exponents = createZeroFilledBaseUnitsMap();

        // replace default base unit exponents from anno, and accumulate prefixes
        UnitsAlias aliasInfo = aliasUnitClass.getAnnotation(UnitsAlias.class);
        for (BaseUnit bu : aliasInfo.value()) {
            exponents.put(bu.unit(), bu.exponent());
            prefix += bu.prefix();
        }

        unitsAnnotationMirrorMap.put(aliasUnitAM, createInternalUnit(
                aliasUnitClass.getCanonicalName(), false, false, prefix, exponents));
    }
    //
    // /**
    // * Creates an internal unit representation for the given alias AnnotationMirror and its
    // * component UnitsAlias meta annotation, adds it to the alias map, and returns the internal
    // * representation.
    // *
    // * @param aliasAnno an {@link AnnotationMirror} of an alias annotation
    // * @param aliasMetaAnno the {@link UnitsAlias} meta annotation of the given alias annotation
    // * @return the internal representation unit as an {@link AnnotationMirror}
    // */
    // public AnnotationMirror createInternalAliasUnit(AnnotationMirror aliasAnno,
    // AnnotationMirror aliasMetaAnno) {
    // // check to see if the annotation has already been mapped before
    // // we search based on the string name of the annotation
    // String fullAnnotationName = aliasAnno.toString();
    // for (AnnotationMirror unit : unitsAnnotationMirrorMap.keySet()) {
    // if (fullAnnotationName.contentEquals(unit.toString())) {
    // return unitsAnnotationMirrorMap.get(unit);
    // }
    // }
    //
    // int prefix = 0;
    //
    // Map<String, Integer> exponents = new TreeMap<>();
    // // default all base units to exponent 0
    // for (String bu : baseUnits()) {
    // exponents.put(bu, 0);
    // }
    // // replace default base unit exponents from anno
    // for (AnnotationMirror bu : AnnotationUtils.getElementValueArray(aliasMetaAnno, "value",
    // AnnotationMirror.class, true)) {
    // exponents.put(AnnotationUtils.getElementValue(bu, "unit", String.class, false),
    // AnnotationUtils.getElementValue(bu, "exponent", Integer.class, true));
    // prefix += AnnotationUtils.getElementValue(bu, "prefix", Integer.class, true);
    // }
    //
    // unitsAnnotationMirrorMap.put(aliasAnno,
    // createInternalUnit(aliasAnno.toString(), false, false, prefix, exponents));
    //
    // return unitsAnnotationMirrorMap.get(aliasAnno);
    // }

    /**
     * Returns the internal unit representation for the given annotation if it has been created,
     * null otherwise.
     *
     * @param anno an {@link AnnotationMirror} of an annotation
     * @return the internal representation unit as an {@link AnnotationMirror}
     */
    public AnnotationMirror getInternalAliasUnit(AnnotationMirror anno) {
        // check to see if the annotation has already been mapped before
        if (unitsAnnotationMirrorMap.containsKey(anno)) {
            return unitsAnnotationMirrorMap.get(anno);
        }

        return null;
    }

    /**
     * Returns the surface unit representation for the given {@link UnitsInternal} annotation if
     * available, otherwise returns the given annotation unchanged.
     * 
     * @param anno an {@link AnnotationMirror} of a {@link UnitsInternal} annotation
     * @return the surface representation unit if available, otherwise the UnitsInternal annotation
     *         unchanged
     */
    public AnnotationMirror getSurfaceUnit(AnnotationMirror anno) {
        Map<AnnotationMirror, AnnotationMirror> map = getUnitsAliasMapSwapped();
        // Substitutes known annotations with their surface annotations
        if (map.containsKey(anno)) {
            return map.get(anno);
        } else {
            return anno;
        }
    }

    /*
     * It is a units annotation if we have built an alias for it in the past (this includes @m
     * --> @UnitsInternal(..)), or is supported by the qual hierarchy, or it is a @UnitsInternal
     * annotation (with possibly not all base units).
     */
    public boolean isUnitsAnnotation(BaseAnnotatedTypeFactory realTypeFactory,
            AnnotationMirror anno) {
        return unitsAnnotationMirrorMap.keySet().contains(anno)
                || realTypeFactory.isSupportedQualifier(anno)
                || AnnotationUtils.areSameByClass(anno, UnitsInternal.class);
    }

    public boolean hasUnitsAnnotation(BaseAnnotatedTypeFactory realTypeFactory,
            Iterable<? extends AnnotationMirror> annotations) {
        for (AnnotationMirror anno : annotations) {
            if (isUnitsAnnotation(realTypeFactory, anno)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns an immutable map of surface units annotations mapped to their internal units
     */
    public Map<AnnotationMirror, AnnotationMirror> getUnitsAliasMap() {
        return immutableUnitsAnnotationMirrorMap;
    }

    /**
     * Returns an immutable map of internal units mapped to their surface units annotations
     */
    public Map<AnnotationMirror, AnnotationMirror> getUnitsAliasMapSwapped() {
        // update swappedMap if there's differences in value set size
        if (unitsAnnotationMirrorMap.values().size() != swappedMap.keySet().size()) {
            swappedMap.putAll(unitsAnnotationMirrorMap.entrySet().stream()
                    .collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));
        }
        return immutableSwappedMap;
    }

    public boolean hasAllBaseUnits(AnnotationMirror anno) {
        if (!AnnotationUtils.areSameByClass(anno, UnitsInternal.class)) {
            return false;
        }

        // add declared base units from the anno to the map, filtering out duplicate base units
        Map<String, Integer> baseUnitsFromAnno = new HashMap<>();
        for (AnnotationMirror buAnno : AnnotationUtils.getElementValueArray(anno, "baseUnits",
                AnnotationMirror.class, true)) {
            String baseUnit = AnnotationUtils.getElementValue(buAnno, "unit", String.class, false);
            int exponent =
                    AnnotationUtils.getElementValue(buAnno, "exponent", Integer.class, false);
            // ensure the declared base unit is actually a supported base unit
            if (!baseUnits().contains(baseUnit)) {
                return false;
            }
            baseUnitsFromAnno.put(baseUnit, exponent);
        }

        // see if it has all of the base unit annotations
        return baseUnitsFromAnno.size() == baseUnits().size();
    }

    private final Map<AnnotationMirror, AnnotationMirror> fillMissingBaseUnitsCache =
            new HashMap<>();

    // Builds a fresh AnnotationMirror for the given annotation with any missing base units filled
    // in

    // TODO: merge with below
    // create an uncached TypeCheckUnits as a "struct" to hold the integers etc
    public AnnotationMirror fillMissingBaseUnits(AnnotationMirror anno) {
        if (AnnotationUtils.areSameByClass(anno, UnitsInternal.class)) {
            if (fillMissingBaseUnitsCache.containsKey(anno)) {
                return fillMissingBaseUnitsCache.get(anno);
            }

            String originalName =
                    AnnotationUtils.getElementValue(anno, "originalName", String.class, true);
            boolean unknownUnits =
                    AnnotationUtils.getElementValue(anno, "unknownUnits", Boolean.class, true);
            boolean unitsBottom =
                    AnnotationUtils.getElementValue(anno, "unitsBottom", Boolean.class, true);
            int prefixExponent =
                    AnnotationUtils.getElementValue(anno, "prefixExponent", Integer.class, true);

            Map<String, Integer> exponents = createZeroFilledBaseUnitsMap();

            // replace base units with values in annotation
            for (AnnotationMirror bu : AnnotationUtils.getElementValueArray(anno, "baseUnits",
                    AnnotationMirror.class, true)) {
                exponents.put(AnnotationUtils.getElementValue(bu, "unit", String.class, false),
                        AnnotationUtils.getElementValue(bu, "exponent", Integer.class, false));
            }

            AnnotationMirror filledInAM = createInternalUnit(originalName, unknownUnits,
                    unitsBottom, prefixExponent, exponents);

            fillMissingBaseUnitsCache.put(anno, filledInAM);

            return filledInAM;
        } else {
            // not an internal units annotation
            return null;
        }
    }

    // A 1 to 1 mapping between an annotation mirror and its unique typecheck unit.
    private final Map<AnnotationMirror, TypecheckUnit> typecheckUnitCache = new HashMap<>();

    public TypecheckUnit createTypecheckUnit(AnnotationMirror anno) {
        if (typecheckUnitCache.containsKey(anno)) {
            return typecheckUnitCache.get(anno);
        }

        TypecheckUnit unit = new TypecheckUnit();

        if (AnnotationUtils.areSameByClass(anno, UnitsInternal.class)) {
            unit.setOriginalName(
                    AnnotationUtils.getElementValue(anno, "originalName", String.class, true));
            unit.setUnknownUnits(
                    AnnotationUtils.getElementValue(anno, "unknownUnits", Boolean.class, true));
            unit.setUnitsBottom(
                    AnnotationUtils.getElementValue(anno, "unitsBottom", Boolean.class, true));
            unit.setPrefixExponent(
                    AnnotationUtils.getElementValue(anno, "prefixExponent", Integer.class, true));

            Map<String, Integer> exponents = new TreeMap<>();
            // default all base units to exponent 0
            for (String bu : baseUnits()) {
                exponents.put(bu, 0);
            }
            // replace base units with values in annotation
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

        return unit;
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
        return builder.build();
    }
}
