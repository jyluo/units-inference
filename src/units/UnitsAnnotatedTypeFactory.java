package units;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import java.lang.annotation.Annotation;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Name;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.qual.LiteralKind;
import org.checkerframework.framework.qual.TypeUseLocation;
import org.checkerframework.framework.type.AnnotatedTypeFormatter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotationClassLoader;
import org.checkerframework.framework.type.DefaultAnnotatedTypeFormatter;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.AnnotationFormatter;
import org.checkerframework.framework.util.GraphQualifierHierarchy;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.BugInCF;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;
import units.qual.BaseUnit;
import units.qual.UnitsAlias;
import units.qual.UnitsInternal;
import units.representation.UnitsRepresentationUtils;
import units.util.UnitsTypecheckUtils;

public class UnitsAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {
    // static reference to the singleton instance
    protected static UnitsRepresentationUtils unitsRepUtils;

    public UnitsAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker, true);
        unitsRepUtils = UnitsRepresentationUtils.getInstance(processingEnv, elements);
        postInit();

        // add implicits for exceptions
        addTypeNameImplicit(java.lang.Exception.class, unitsRepUtils.DIMENSIONLESS);
        addTypeNameImplicit(java.lang.Throwable.class, unitsRepUtils.DIMENSIONLESS);
        addTypeNameImplicit(java.lang.Void.class, unitsRepUtils.BOTTOM);
    }

    @Override
    protected AnnotationClassLoader createAnnotationClassLoader() {
        // Use the Units Annotated Type Loader instead of the default one
        return new UnitsAnnotationClassLoader(checker);
    }

    @Override
    protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
        // get all the loaded annotations
        Set<Class<? extends Annotation>> qualSet = new HashSet<Class<? extends Annotation>>();
        qualSet.addAll(getBundledTypeQualifiersWithPolyAll());

        // // load all the external units
        // loadAllExternalUnits();
        //
        // // copy all loaded external Units to qual set
        // qualSet.addAll(externalQualsMap.values());

        // create internal use annotation mirrors using the base units that have been initialized.
        // must be called here as other methods called within ATF.postInit() requires the annotation
        // mirrors
        unitsRepUtils.postInit();
        // and it should already have some base units
        assert !unitsRepUtils.baseUnits().isEmpty();

        return qualSet;
    }

    @Override
    public AnnotationMirror aliasedAnnotation(AnnotationMirror anno) {
        // check to see if it is an internal units annotation
        if (AnnotationUtils.areSameByClass(anno, UnitsInternal.class)) {
            // fill in missing base units
            return unitsRepUtils.fillMissingBaseUnits(anno);
        }

        // check to see if it's a surface annotation such as @m or @UnknownUnits
        for (AnnotationMirror metaAnno :
                anno.getAnnotationType().asElement().getAnnotationMirrors()) {

            // if it has a UnitsAlias or IsBaseUnit meta-annotation, then it must have been prebuilt
            // return the prebuilt internal annotation
            if (AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)
                    || AnnotationUtils.areSameByClass(metaAnno, BaseUnit.class)) {

                // System.err.println(" returning prebuilt alias for " + anno.toString());

                return unitsRepUtils.getInternalAliasUnit(anno);
            }
        }

        return super.aliasedAnnotation(anno);
    }

    // Make sure only UnitsInternal annotations with all base units defined are considered supported
    // any UnitsInternal annotations without all base units should go through aliasing to have the
    // base units filled in.
    @Override
    public boolean isSupportedQualifier(AnnotationMirror anno) {
        /*
         * getQualifierHierarchy().getTypeQualifiers() contains PolyAll, PolyUnit, and the AMs of
         * Top and Bottom. We need to check all other instances of UnitsInternal AMs that are
         * supported qualifiers here.
         */
        if (!super.isSupportedQualifier(anno)) {
            return false;
        }
        if (AnnotationUtils.areSameByClass(anno, UnitsInternal.class)) {
            return unitsRepUtils.hasAllBaseUnits(anno);
        }
        // Anno is PolyAll, PolyUnit
        return AnnotationUtils.containsSame(this.getQualifierHierarchy().getTypeQualifiers(), anno);
    }

    // Programmatically set the qualifier defaults
    @Override
    protected void addCheckedCodeDefaults(QualifierDefaults defs) {
        // set DIMENSIONLESS as the default qualifier in hierarchy
        defs.addCheckedCodeDefault(unitsRepUtils.DIMENSIONLESS, TypeUseLocation.OTHERWISE);
        // defaults for upper bounds is DIMENSIONLESS, individual bounds can be manually set to
        // UnknownUnits if they want to use units
        // defs.addCheckedCodeDefault(unitsRepUtils.DIMENSIONLESS, TypeUseLocation.UPPER_BOUND);
        defs.addCheckedCodeDefault(
                unitsRepUtils.DIMENSIONLESS, TypeUseLocation.EXPLICIT_UPPER_BOUND);
        defs.addCheckedCodeDefault(unitsRepUtils.TOP, TypeUseLocation.IMPLICIT_UPPER_BOUND);
        // defaults for lower bounds is BOTTOM, individual bounds can be manually set
        defs.addCheckedCodeDefault(unitsRepUtils.BOTTOM, TypeUseLocation.LOWER_BOUND);
        // exceptions are always dimensionless
        defs.addCheckedCodeDefault(
                unitsRepUtils.DIMENSIONLESS, TypeUseLocation.EXCEPTION_PARAMETER);
        // set TOP as the default qualifier for local variables, for dataflow refinement
        defs.addCheckedCodeDefault(unitsRepUtils.TOP, TypeUseLocation.LOCAL_VARIABLE);
    }

    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new UnitsQualifierHierarchy(factory);
    }

    private final class UnitsQualifierHierarchy extends GraphQualifierHierarchy {
        public UnitsQualifierHierarchy(MultiGraphFactory mgf) {
            super(mgf, unitsRepUtils.BOTTOM);
        }

        // Programmatically set UnitsRepresentationUtils.BOTTOM as the bottom
        @Override
        protected Set<AnnotationMirror> findBottoms(
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypes) {
            Set<AnnotationMirror> newBottoms = super.findBottoms(supertypes);
            newBottoms.remove(unitsRepUtils.RAWUNITSINTERNAL);
            newBottoms.add(unitsRepUtils.BOTTOM);

            // set direct supertypes of bottom
            Set<AnnotationMirror> supertypesOfBottom = new LinkedHashSet<>();
            supertypesOfBottom.add(unitsRepUtils.TOP);
            supertypes.put(unitsRepUtils.BOTTOM, supertypesOfBottom);

            return newBottoms;
        }

        // Programmatically set UnitsRepresentationUtils.TOP as the top
        @Override
        protected void finish(
                QualifierHierarchy qualHierarchy,
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypesMap,
                Map<AnnotationMirror, AnnotationMirror> polyQualifiers,
                Set<AnnotationMirror> tops,
                Set<AnnotationMirror> bottoms,
                Object... args) {
            super.finish(qualHierarchy, supertypesMap, polyQualifiers, tops, bottoms, args);

            // System.err.println(" === ATF ");
            // System.err.println(" pre - fullMap " + fullMap);

            // swap every instance of RAWUNITSINTERNAL with TOP
            assert supertypesMap.containsKey(unitsRepUtils.RAWUNITSINTERNAL);
            // Set direct supertypes of TOP
            supertypesMap.put(unitsRepUtils.TOP, supertypesMap.get(unitsRepUtils.RAWUNITSINTERNAL));
            supertypesMap.remove(unitsRepUtils.RAWUNITSINTERNAL);

            // Set direct supertypes of PolyAll
            // replace raw UnitsInternal with UnitsTop in super of PolyAll
            assert supertypesMap.containsKey(unitsRepUtils.POLYALL);
            Set<AnnotationMirror> polyAllSupers = AnnotationUtils.createAnnotationSet();
            polyAllSupers.addAll(supertypesMap.get(unitsRepUtils.POLYALL));
            polyAllSupers.add(unitsRepUtils.TOP);
            polyAllSupers.remove(unitsRepUtils.RAWUNITSINTERNAL);
            supertypesMap.put(unitsRepUtils.POLYALL, Collections.unmodifiableSet(polyAllSupers));

            // Set direct supertypes of PolyUnit
            // replace raw UnitsInternal with UnitsTop in super of PolyUnit
            assert supertypesMap.containsKey(unitsRepUtils.POLYUNIT);
            Set<AnnotationMirror> polyUnitSupers = AnnotationUtils.createAnnotationSet();
            polyUnitSupers.addAll(supertypesMap.get(unitsRepUtils.POLYUNIT));
            polyUnitSupers.add(unitsRepUtils.TOP);
            polyUnitSupers.remove(unitsRepUtils.RAWUNITSINTERNAL);
            supertypesMap.put(unitsRepUtils.POLYUNIT, Collections.unmodifiableSet(polyUnitSupers));

            // Set direct supertypes of BOTTOM
            Set<AnnotationMirror> bottomSupers = AnnotationUtils.createAnnotationSet();
            bottomSupers.addAll(supertypesMap.get(unitsRepUtils.BOTTOM));
            // bottom already has top in its super set
            bottomSupers.remove(unitsRepUtils.RAWUNITSINTERNAL);
            supertypesMap.put(unitsRepUtils.BOTTOM, Collections.unmodifiableSet(bottomSupers));

            // Update polyQualifiers
            assert polyQualifiers.containsKey(unitsRepUtils.RAWUNITSINTERNAL);
            polyQualifiers.put(
                    unitsRepUtils.TOP, polyQualifiers.get(unitsRepUtils.RAWUNITSINTERNAL));
            polyQualifiers.remove(unitsRepUtils.RAWUNITSINTERNAL);

            // Update tops
            tops.remove(unitsRepUtils.RAWUNITSINTERNAL);
            tops.add(unitsRepUtils.TOP);

            // System.err.println(" === Typecheck ATF ");
            // System.err.println(" supertypesMap ");
            // for (Entry<?, ?> e : supertypesMap.entrySet()) {
            // System.err.println(" " + e.getKey() + " -> " + e.getValue());
            // }
            // System.err.println(" polyQualifiers " + polyQualifiers);
            // System.err.println(" tops " + tops);
            // System.err.println(" bottoms " + bottoms);
        }

        @Override
        public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
            // System.err.println(" === checking SUBTYPE \n "
            // + getAnnotationFormatter().formatAnnotationMirror(subAnno) + " <:\n"
            // + getAnnotationFormatter().formatAnnotationMirror(superAnno) + "\n");

            // replace raw @UnitsInternal with Dimensionless
            // for some reason this shows up in inference mode when building the lattice
            if (AnnotationUtils.areSame(subAnno, unitsRepUtils.RAWUNITSINTERNAL)) {
                subAnno = unitsRepUtils.DIMENSIONLESS;
            }
            if (AnnotationUtils.areSame(superAnno, unitsRepUtils.RAWUNITSINTERNAL)) {
                superAnno = unitsRepUtils.DIMENSIONLESS;
            }

            // Case: All units <: Top
            if (AnnotationUtils.areSame(superAnno, unitsRepUtils.TOP)) {
                return true;
            }

            // Case: Bottom <: All units
            if (AnnotationUtils.areSame(subAnno, unitsRepUtils.BOTTOM)) {
                return true;
            }

            // Case: @PolyAll <: All units
            // Case: @PolyUnit <: PolyAll and All units
            // Case: All units <: @PolyAll and @PolyUnit
            if (AnnotationUtils.areSame(subAnno, unitsRepUtils.POLYALL)
                    || AnnotationUtils.areSame(subAnno, unitsRepUtils.POLYUNIT)
                    || AnnotationUtils.areSame(superAnno, unitsRepUtils.POLYALL)
                    || AnnotationUtils.areSame(superAnno, unitsRepUtils.POLYUNIT)) {
                return true;
            }

            // Case: @UnitsInternal(x) <: @UnitsInternal(y)
            if (AnnotationUtils.areSameByClass(subAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameByClass(superAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameIgnoringValues(subAnno, superAnno)) {

                boolean result = UnitsTypecheckUtils.unitsEqual(subAnno, superAnno);

                // if (AnnotationUtils.areSame(superAnno, unitsRepUtils.METER)) {
                // System.err.println(" === checking SUBTYPE \n "
                // + getAnnotationFormatter().formatAnnotationMirror(subAnno) + " <:\n"
                // + getAnnotationFormatter().formatAnnotationMirror(superAnno) + "\n"
                // + " result: " + result);
                // }

                return result;
            }

            throw new BugInCF(
                    "Uncaught subtype check case:"
                            + "\n    subtype:   "
                            + getAnnotationFormatter().formatAnnotationMirror(subAnno)
                            + "\n    supertype: "
                            + getAnnotationFormatter().formatAnnotationMirror(superAnno));
        }
    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(
                new UnitsTypecheckImplicitsTreeAnnotator(), new UnitsPropagationTreeAnnotator());
    }

    protected final class UnitsTypecheckImplicitsTreeAnnotator extends UnitsImplicitsTreeAnnotator {
        // Programmatically set the qualifier implicits
        public UnitsTypecheckImplicitsTreeAnnotator() {
            super(UnitsAnnotatedTypeFactory.this);
            // in type checking mode, we also set dimensionless for the number literals
            addLiteralKind(LiteralKind.INT, unitsRepUtils.DIMENSIONLESS);
            addLiteralKind(LiteralKind.LONG, unitsRepUtils.DIMENSIONLESS);
            addLiteralKind(LiteralKind.FLOAT, unitsRepUtils.DIMENSIONLESS);
            addLiteralKind(LiteralKind.DOUBLE, unitsRepUtils.DIMENSIONLESS);
        }

        /**
         * HACK: Replace the types of the enum constants in {@link java.util.concurrent.TimeUnit}.
         *
         * <p>TODO: the cleaner way would be to support annotating enum constants via stubs;
         * currently unavailable as a feature.
         */
        @Override
        void replaceEnumConstantType(Name name, AnnotatedTypeMirror atm) {
            if (TypesUtils.isDeclaredOfName(
                    atm.getUnderlyingType(),
                    java.util.concurrent.TimeUnit.class.getCanonicalName())) {
                switch (name.toString()) {
                    case "NANOSECONDS":
                        atm.replaceAnnotation(unitsRepUtils.NANOSECOND);
                        break;
                    case "MICROSECONDS":
                        atm.replaceAnnotation(unitsRepUtils.MICROSECOND);
                        break;
                    case "MILLISECONDS":
                        atm.replaceAnnotation(unitsRepUtils.MILLISECOND);
                        break;
                    case "SECONDS":
                        atm.replaceAnnotation(unitsRepUtils.SECOND);
                        break;
                    default:
                        // TODO: MINUTES, HOURS, DAYS
                        break;
                }
            }
        }
    }

    private final class UnitsPropagationTreeAnnotator extends PropagationTreeAnnotator {
        public UnitsPropagationTreeAnnotator() {
            super(UnitsAnnotatedTypeFactory.this);
        }

        @Override
        public Void visitBinary(BinaryTree binaryTree, AnnotatedTypeMirror type) {
            Kind kind = binaryTree.getKind();
            AnnotatedTypeMirror lhsATM = atypeFactory.getAnnotatedType(binaryTree.getLeftOperand());
            AnnotatedTypeMirror rhsATM =
                    atypeFactory.getAnnotatedType(binaryTree.getRightOperand());
            AnnotationMirror lhsAM = lhsATM.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);
            AnnotationMirror rhsAM = rhsATM.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);

            switch (kind) {
                case PLUS:
                    // if it is a string concatenation, result is dimensionless
                    if (TreeUtils.isStringConcatenation(binaryTree)) {
                        type.replaceAnnotation(unitsRepUtils.DIMENSIONLESS);
                    } else {
                        type.replaceAnnotation(
                                atypeFactory.getQualifierHierarchy().leastUpperBound(lhsAM, rhsAM));
                    }
                    //
                    // else if (AnnotationUtils.areSame(lhsAM, rhsAM)) {
                    // type.replaceAnnotation(lhsAM);
                    // } else {
                    // type.replaceAnnotation(unitsRepUtils.TOP);
                    // }
                    break;
                case MINUS:
                    // if (AnnotationUtils.areSame(lhsAM, rhsAM)) {
                    // type.replaceAnnotation(lhsAM);
                    // } else {
                    // type.replaceAnnotation(unitsRepUtils.TOP);
                    // }
                    type.replaceAnnotation(
                            atypeFactory.getQualifierHierarchy().leastUpperBound(lhsAM, rhsAM));
                    break;
                case MULTIPLY:
                    type.replaceAnnotation(UnitsTypecheckUtils.multiplication(lhsAM, rhsAM));
                    break;
                case DIVIDE:
                    type.replaceAnnotation(UnitsTypecheckUtils.division(lhsAM, rhsAM));
                    break;
                case REMAINDER:
                    type.replaceAnnotation(lhsAM);
                    break;
                case CONDITIONAL_AND: // &&
                case CONDITIONAL_OR: // ||
                case LOGICAL_COMPLEMENT: // !
                case EQUAL_TO: // ==
                case NOT_EQUAL_TO: // !=
                case GREATER_THAN: // >
                case GREATER_THAN_EQUAL: // >=
                case LESS_THAN: // <
                case LESS_THAN_EQUAL: // <=
                    // output of comparisons is a dimensionless binary
                    type.replaceAnnotation(unitsRepUtils.DIMENSIONLESS);
                    break;
                default:
                    // Check LUB by default
                    return super.visitBinary(binaryTree, type);
            }

            return null;
        }
    }

    // for use in AnnotatedTypeMirror.toString()
    @Override
    protected AnnotatedTypeFormatter createAnnotatedTypeFormatter() {
        return new DefaultAnnotatedTypeFormatter(
                createAnnotationFormatter(),
                checker.hasOption("printVerboseGenerics"),
                checker.hasOption("printAllQualifiers"));
    }

    // for use in generating error outputs
    @Override
    protected AnnotationFormatter createAnnotationFormatter() {
        return new UnitsAnnotationFormatter(checker);
    }
}
