package units.utils;

import java.lang.annotation.Annotation;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.util.Elements;
import org.checkerframework.framework.qual.PolyAll;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.util.AnnotationMirrorMap;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.BugInCF;
import units.UnitsAnnotationClassLoader;
import units.qual.BUC;
import units.qual.Dimensionless;
import units.qual.PolyUnit;
import units.qual.UnitsAlias;
import units.qual.UnitsBottom;
import units.qual.UnitsRep;
import units.qual.UnknownUnits;

/**
 * Utility class containing logic for creating, updating, and converting internal representations of
 * units between its 2 primary forms: {@link UnitsRep} as annotation mirrors and {@link
 * TypecheckUnit}.
 */
public class UnitsRepresentationUtils {
    protected ProcessingEnvironment processingEnv;
    protected Elements elements;

    /** An instance of {@link PolyAll} as an {@link AnnotationMirror} */
    public AnnotationMirror POLYALL;

    /** An instance of {@link PolyUnit} as an {@link AnnotationMirror} */
    public AnnotationMirror POLYUNIT;

    /** An instance of {@link UnitsRep} with no values in its elements */
    public AnnotationMirror RAWUNITSREP;

    /** An instance of {@link UnitsRep} with values to represent {@link UnknownUnits} */
    public AnnotationMirror TOP;

    /** An instance of {@link UnitsRep} with values to represent {@link UnitsBottom} */
    public AnnotationMirror BOTTOM;

    /**
     * An instance of {@link UnitsRep} with default values in its elements, to represent {@link
     * Dimensionless}
     */
    public AnnotationMirror DIMENSIONLESS;

    /**
     * A 1 to 1 mapping between a (possibly incomplete) {@link UnitsRep} annotation mirror and its
     * corresponding {@link UnitsRep} annotation mirror with all base units filled in and set to 0
     */
    protected final AnnotationMirrorMap<AnnotationMirror> unitsRepToCompleteUnitsRepMap =
            new AnnotationMirrorMap<>();

    /**
     * A 1 to 1 mapping between a {@link UnitsRep} annotation mirror and its corresponding typecheck
     * unit.
     */
    protected final AnnotationMirrorMap<TypecheckUnit> unitsRepAnnoToTypecheckUnitMap =
            new AnnotationMirrorMap<>();

    /**
     * A 1 to 1 mapping between a {@link UnitsRep} annotation mirror and its corresponding typecheck
     * unit for pretty printing: the {@link UnitsRep} annotation mirror omits default annotation
     * values.
     */
    protected final AnnotationMirrorMap<TypecheckUnit> prettyPrintUnitsRepAnnoToTypecheckUnitMap =
            new AnnotationMirrorMap<>();

    /** The set of base units */
    protected final Map<String, Class<? extends Annotation>> baseUnits = new TreeMap<>();

    /** All base units provided by the checker or user */
    protected Set<String> baseUnitNames;

    /** Comparator used to sort annotation classes by their simple class name. */
    protected static Comparator<Class<? extends Annotation>> annoClassComparator =
            new Comparator<Class<? extends Annotation>>() {
                @Override
                public int compare(Class<? extends Annotation> a1, Class<? extends Annotation> a2) {
                    return a1.getSimpleName().compareTo(a2.getSimpleName());
                }
            };

    /** The set of alias units, sorted by their simple class name. */
    protected final Set<Class<? extends Annotation>> aliasUnits = createSortedBaseUnitSet();

    /** A map from surface units annotation mirrors to their {@link UnitsRep}s representation. */
    protected final AnnotationMirrorMap<AnnotationMirror> unitsAnnotationMirrorMap =
            new AnnotationMirrorMap<>();

    public UnitsRepresentationUtils(ProcessingEnvironment processingEnv, Elements elements) {
        this.processingEnv = processingEnv;
        this.elements = elements;
    }

    /**
     * Creates {@link AnnotationMirror}s for all of the annotations in this class
     *
     * @param loadedBaseUnits the set of base units loaded by {@link UnitsAnnotationClassLoader}
     * @param loadedAliasUnits the set of alias units loaded by {@link UnitsAnnotationClassLoader}
     */
    public void postInit(
            Set<Class<? extends Annotation>> loadedBaseUnits,
            Set<Class<? extends Annotation>> loadedAliasUnits) {

        // Create and add annotation mirrors for loaded base units and alias units
        // First add all the base units so that the size of the base unit exponent map is correct
        for (Class<? extends Annotation> baseUnit : loadedBaseUnits) {
            addBaseUnit(baseUnit);
        }
        // Then create {@link UnitsRep} annotation mirrors for each base unit
        for (Class<? extends Annotation> baseUnit : loadedBaseUnits) {
            createInternalBaseUnit(baseUnit);
        }
        // Finally add and create {@link UnitsRep} annotation mirrors for each alias unit
        for (Class<? extends Annotation> aliasUnit : loadedAliasUnits) {
            addAliasUnit(aliasUnit);
            createInternalAliasUnit(aliasUnit);
        }

        POLYALL = AnnotationBuilder.fromClass(elements, PolyAll.class);
        POLYUNIT = AnnotationBuilder.fromClass(elements, PolyUnit.class);

        RAWUNITSREP = AnnotationBuilder.fromClass(elements, UnitsRep.class);

        // Create and add annotation mirrors for TOP, BOT, and DIMENSIONLESS
        Map<String, Integer> zeroBaseDimensions = createZeroFilledBaseUnitsMap();
        TOP = createUnitsRepAnno(true, false, 0, zeroBaseDimensions);
        BOTTOM = createUnitsRepAnno(false, true, 0, zeroBaseDimensions);
        DIMENSIONLESS = createUnitsRepAnno(false, false, 0, zeroBaseDimensions);

        unitsAnnotationMirrorMap.put(
                AnnotationBuilder.fromClass(elements, UnknownUnits.class), TOP);
        unitsAnnotationMirrorMap.put(
                AnnotationBuilder.fromClass(elements, UnitsBottom.class), BOTTOM);
        unitsAnnotationMirrorMap.put(
                AnnotationBuilder.fromClass(elements, Dimensionless.class), DIMENSIONLESS);

        // for (Entry<?, ?> entry : unitsAnnotationMirrorMap.entrySet()) {
        // System.err.println(" == built map " + entry.getKey() + " --> " + entry.getValue());
        // }
    }

    public Set<Class<? extends Annotation>> createSortedBaseUnitSet() {
        return new TreeSet<>(annoClassComparator);
    }

    public <TVal> Map<String, TVal> createSortedBaseUnitMap() {
        return new TreeMap<>();
    }

    public void addBaseUnit(Class<? extends Annotation> baseUnit) {
        baseUnits.put(baseUnit.getSimpleName(), baseUnit);
    }

    public Set<String> baseUnits() {
        if (baseUnitNames == null) {
            baseUnitNames = Collections.unmodifiableSet(baseUnits.keySet());
        }
        return baseUnitNames;
    }

    public void addAliasUnit(Class<? extends Annotation> aliasUnit) {
        aliasUnits.add(aliasUnit);
    }

    /**
     * Creates and returns an exponent values map with all defined base units sorted alphabetically
     * according to unit symbol name, and with the exponent values set to 0.
     */
    protected Map<String, Integer> createZeroFilledBaseUnitsMap() {
        Map<String, Integer> map = createSortedBaseUnitMap();
        for (String baseUnit : baseUnits()) {
            map.put(baseUnit, 0);
        }
        return map;
    }

    /**
     * Creates an {@link UnitsRep} representation for the given base unit and adds it to the alias
     * map.
     */
    protected void createInternalBaseUnit(Class<? extends Annotation> baseUnitClass) {
        // check to see if the annotation has already been mapped before
        AnnotationMirror baseUnitAM = AnnotationBuilder.fromClass(elements, baseUnitClass);
        if (unitsAnnotationMirrorMap.containsKey(baseUnitAM)) {
            return;
        }

        Map<String, Integer> exponents = createZeroFilledBaseUnitsMap();

        // set the exponent of the given base unit to 1
        exponents.put(baseUnitClass.getSimpleName(), 1);
        // create the {@link UnitsRep} and add to alias map
        unitsAnnotationMirrorMap.put(baseUnitAM, createUnitsRepAnno(false, false, 0, exponents));
    }

    /**
     * Creates an {@link UnitsRep} representation for the given alias unit and adds it to the alias
     * map.
     */
    protected void createInternalAliasUnit(Class<? extends Annotation> aliasUnitClass) {
        // check to see if the annotation has already been mapped before
        AnnotationMirror aliasUnitAM = AnnotationBuilder.fromClass(elements, aliasUnitClass);
        if (unitsAnnotationMirrorMap.containsKey(aliasUnitAM)) {
            return;
        }

        Map<String, Integer> exponents = createZeroFilledBaseUnitsMap();

        // replace default base unit exponents from anno, and accumulate prefixes
        UnitsAlias unitsRep = aliasUnitClass.getAnnotation(UnitsAlias.class);
        for (BUC baseUnitComponent : unitsRep.bu()) {
            exponents.put(baseUnitComponent.u(), baseUnitComponent.e());
        }

        int prefix = unitsRep.p();

        unitsAnnotationMirrorMap.put(
                aliasUnitAM, createUnitsRepAnno(false, false, prefix, exponents));
    }

    /**
     * Returns the {@link UnitsRep} representation for the given surface annotation if it has been
     * created, null otherwise.
     *
     * @param anno an {@link AnnotationMirror} of an annotation
     * @return the internal representation unit as an {@link AnnotationMirror}
     */
    public AnnotationMirror getUnitsRepAnno(AnnotationMirror anno) {
        // check to see if the annotation has already been mapped before
        if (unitsAnnotationMirrorMap.containsKey(anno)) {
            return unitsAnnotationMirrorMap.get(anno);
        }

        return null;
    }

    /**
     * Returns the surface unit representation for the given {@link UnitsRep} annotation if
     * available, otherwise returns the given annotation unchanged.
     *
     * @param anno an {@link AnnotationMirror} of a {@link UnitsRep} annotation
     * @return the surface representation unit if available, otherwise the {@link UnitsRep}
     *     annotation unchanged
     */
    public AnnotationMirror getSurfaceUnit(AnnotationMirror anno) {
        for (Entry<AnnotationMirror, AnnotationMirror> pair : unitsAnnotationMirrorMap.entrySet()) {
            if (AnnotationUtils.areSame(pair.getValue(), anno)) {
                return pair.getKey();
            }
        }

        return anno;
    }

    /**
     * Returns a pretty print unit representation for the given {@link UnitsRep} annotation with all
     * default annotation values omitted, if available, otherwise returns the given annotation
     * unchanged.
     *
     * @param anno an {@link AnnotationMirror} of a {@link UnitsRep} annotation
     * @return the pretty print representation unit if available, otherwise the {@link UnitsRep}
     *     annotation unchanged
     */
    public AnnotationMirror getPrettyPrintUnit(AnnotationMirror anno) {
        AnnotationMirror surfaceUnit = getSurfaceUnit(anno);
        // if surfaceUnit is the same as anno, then remove all default annotation values
        if (AnnotationUtils.areSameByClass(surfaceUnit, UnitsRep.class)) {
            TypecheckUnit unit = createTypecheckUnit(surfaceUnit);
            AnnotationMirror prettyPrintUnit = createPrettyPrintUnitsRepAnno(unit);
            return prettyPrintUnit;
        } else {
            return surfaceUnit;
        }
    }

    /**
     * The given annotation is a units annotation if we have built an alias for it in the past (this
     * includes {@code @m --> @UnitsRep(..)}), or is supported by the qual hierarchy, or it is a
     * {@link UnitsRep} annotation.
     *
     * @param atf AnnotatedTypeFactory
     * @param anno an annotation to check
     * @return whether the given annotation is a units annotation
     */
    public boolean isUnitsAnnotation(AnnotatedTypeFactory atf, AnnotationMirror anno) {
        return unitsAnnotationMirrorMap.keySet().contains(anno)
                || atf.isSupportedQualifier(anno)
                || AnnotationUtils.areSameByClass(anno, UnitsRep.class);
    }

    /**
     * the given collection of annotations contains a units annotation if at least one of its
     * annotation is a units annotation according to {@link #isUnitsAnnotation(AnnotatedTypeFactory,
     * AnnotationMirror)}
     *
     * @param atf
     * @param annotations a collection of annotations
     * @return whether the given collection of annotations contains a units annotation
     */
    public boolean hasUnitsAnnotation(
            AnnotatedTypeFactory atf, Collection<? extends AnnotationMirror> annotations) {
        for (AnnotationMirror anno : annotations) {
            if (isUnitsAnnotation(atf, anno)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return whether the given {@link UnitsRep} annotation expresses an exponent for all base
     *     units.
     */
    public boolean hasAllBaseUnits(AnnotationMirror anno) {
        if (!AnnotationUtils.areSameByClass(anno, UnitsRep.class)) {
            return false;
        }

        // add declared base units from the anno to the map, filtering out duplicate base units
        Map<String, Integer> baseUnitsFromAnno = new HashMap<>();
        for (AnnotationMirror buAnno :
                AnnotationUtils.getElementValueArray(anno, "bu", AnnotationMirror.class, true)) {
            String baseUnit = AnnotationUtils.getElementValue(buAnno, "u", String.class, false);
            int exponent = AnnotationUtils.getElementValue(buAnno, "e", Integer.class, false);
            // ensure the declared base unit is actually a supported base unit
            if (!baseUnits().contains(baseUnit)) {
                return false;
            }
            baseUnitsFromAnno.put(baseUnit, exponent);
        }

        // see if it has all of the base unit annotations
        return baseUnitsFromAnno.size() == baseUnits().size();
    }

    /**
     * Builds a fresh {@link UnitsRep} annotation for the given {@link UnitsRep} annotation with any
     * missing base units filled in. For all other annotations, this method returns null.
     */
    public AnnotationMirror fillMissingBaseUnits(AnnotationMirror anno) {
        if (AnnotationUtils.areSameByClass(anno, UnitsRep.class)) {
            if (unitsRepToCompleteUnitsRepMap.containsKey(anno)) {
                return unitsRepToCompleteUnitsRepMap.get(anno);
            }

            TypecheckUnit unit = createTypecheckUnitNoCache(anno);
            AnnotationMirror filledInAM = createUnitsRepAnno(unit);

            unitsRepToCompleteUnitsRepMap.put(anno, filledInAM);

            return filledInAM;
        } else {
            // not a {@link UnitsRep} annotation
            return null;
        }
    }

    /**
     * Create a {@link TypecheckUnit} for the given complete {@link UnitsRep} annotation and caches
     * the pair.
     */
    public TypecheckUnit createTypecheckUnit(AnnotationMirror anno) {
        if (unitsRepAnnoToTypecheckUnitMap.containsKey(anno)) {
            return unitsRepAnnoToTypecheckUnitMap.get(anno);
        }

        TypecheckUnit unit = createTypecheckUnitNoCache(anno);
        unitsRepAnnoToTypecheckUnitMap.put(anno, unit);
        return unit;
    }

    /** Create a {@link TypecheckUnit} for the given {@link UnitsRep} annotation. */
    public TypecheckUnit createTypecheckUnitNoCache(AnnotationMirror anno) {
        TypecheckUnit unit = new TypecheckUnit(this);

        // if it is a polymorphic annotation, generate top as we are type checking the body of
        // a polymorphic method
        if (AnnotationUtils.areSameByClass(anno, PolyUnit.class)
                || AnnotationUtils.areSameByClass(anno, PolyAll.class)) {
            unit.setUnknownUnits(true);
            return unit;
        }
        // if it is a {@link UnitsRep} annotation, generate the equivalent {@link TypecheckUnit}
        else if (AnnotationUtils.areSameByClass(anno, UnitsRep.class)) {
            unit.setUnknownUnits(AnnotationUtils.getElementValue(anno, "top", Boolean.class, true));
            unit.setUnitsBottom(AnnotationUtils.getElementValue(anno, "bot", Boolean.class, true));
            unit.setPrefixExponent(AnnotationUtils.getElementValue(anno, "p", Integer.class, true));

            Map<String, Integer> exponents = createSortedBaseUnitMap();
            // default all base units to exponent 0
            for (String bu : baseUnits()) {
                exponents.put(bu, 0);
            }
            // replace base units with values in annotation
            for (AnnotationMirror bu :
                    AnnotationUtils.getElementValueArray(
                            anno, "bu", AnnotationMirror.class, true)) {
                exponents.put(
                        AnnotationUtils.getElementValue(bu, "u", String.class, false),
                        AnnotationUtils.getElementValue(bu, "e", Integer.class, false));
            }

            for (String bu : exponents.keySet()) {
                unit.setExponent(bu, exponents.get(bu));
            }
            return unit;
        } else {
            // not a units annotation
            return null;
        }
    }

    /** Create a {@link UnitsRep} annotation for the given {@link TypecheckUnit}. */
    public AnnotationMirror createUnitsRepAnno(TypecheckUnit unit) {
        // see if cache already has a mapping, if so return from cache
        for (Entry<AnnotationMirror, TypecheckUnit> entry :
                unitsRepAnnoToTypecheckUnitMap.entrySet()) {
            if (unit.equals(entry.getValue())) {
                return entry.getKey();
            }
        }

        // otherwise create an {@link UnitsRep} for the typecheck unit and add to cache
        AnnotationMirror anno =
                createUnitsRepAnno(
                        unit.isTop(),
                        unit.isBottom(),
                        unit.getPrefixExponent(),
                        unit.getExponents());

        unitsRepAnnoToTypecheckUnitMap.put(anno, unit);
        return anno;
    }

    /** Create a {@link UnitsRep} annotation for the given normalized representation values. */
    public AnnotationMirror createUnitsRepAnno(
            boolean t, boolean b, int e, Map<String, Integer> buc) {
        // not allowed to set both a UU and UB to true on the same annotation
        if (t && b) {
            throw new BugInCF("Cannot set top and bottom both to true at the same time");
        }

        AnnotationBuilder builder = new AnnotationBuilder(processingEnv, UnitsRep.class);

        List<AnnotationMirror> bu = new ArrayList<>();
        for (String baseUnit : buc.keySet()) {
            /** Construct {@link BUC} annotations for each exponent */
            AnnotationBuilder bucBuilder = new AnnotationBuilder(processingEnv, BUC.class);
            bucBuilder.setValue("u", baseUnit);
            bucBuilder.setValue("e", buc.get(baseUnit));
            bu.add(bucBuilder.build());
        }

        // See {@link UnitsRep}
        builder.setValue("top", t);
        builder.setValue("bot", b);
        builder.setValue("p", e);
        builder.setValue("bu", bu);
        return builder.build();
    }

    /** Create a {@link UnitsRep} annotation for the given {@link TypecheckUnit}. */
    public AnnotationMirror createPrettyPrintUnitsRepAnno(TypecheckUnit unit) {
        // see if cache already has a mapping, if so return from cache
        for (Entry<AnnotationMirror, TypecheckUnit> entry :
                prettyPrintUnitsRepAnnoToTypecheckUnitMap.entrySet()) {
            if (unit.equals(entry.getValue())) {
                return entry.getKey();
            }
        }

        // otherwise create an {@link UnitsRep} for the typecheck unit and add to cache
        AnnotationMirror anno =
                createPrettyPrintUnitsRepAnno(
                        unit.isTop(),
                        unit.isBottom(),
                        unit.getPrefixExponent(),
                        unit.getExponents());

        prettyPrintUnitsRepAnnoToTypecheckUnitMap.put(anno, unit);
        return anno;
    }

    /** Create a {@link UnitsRep} annotation for the given normalized representation values. */
    public AnnotationMirror createPrettyPrintUnitsRepAnno(
            boolean t, boolean b, int e, Map<String, Integer> buc) {
        // not allowed to set both a UU and UB to true on the same annotation
        if (t && b) {
            throw new BugInCF("Cannot set top and bottom both to true at the same time");
        }

        AnnotationBuilder builder = new AnnotationBuilder(processingEnv, UnitsRep.class);

        List<AnnotationMirror> bu = new ArrayList<>();
        for (String baseUnit : buc.keySet()) {
            int exponent = buc.get(baseUnit);
            if (exponent != 0) {
                /** Construct {@link BUC} annotations for each exponent */
                AnnotationBuilder bucBuilder = new AnnotationBuilder(processingEnv, BUC.class);
                bucBuilder.setValue("u", baseUnit);
                bucBuilder.setValue("e", exponent);
                bu.add(bucBuilder.build());
            }
        }

        // See {@link UnitsRep}
        if (t) builder.setValue("top", t);
        if (b) builder.setValue("bot", b);
        if (e != 0) builder.setValue("p", e);
        if (!bu.isEmpty()) builder.setValue("bu", bu);
        return builder.build();
    }

    /**
     * Checks to see if the given anno is {@link PolyAll} or {@link PolyUnit}
     *
     * @param anno
     * @return true if the anno is either of the polymorphic annotations
     */
    public boolean isPolymorphic(AnnotationMirror anno) {
        return AnnotationUtils.areSame(anno, POLYALL) || AnnotationUtils.areSame(anno, POLYUNIT);
    }
}
