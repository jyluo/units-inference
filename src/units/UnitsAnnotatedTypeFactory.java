package units;

import java.lang.annotation.Annotation;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.qual.PolyAll;
import org.checkerframework.framework.qual.TypeUseLocation;
import org.checkerframework.framework.type.AnnotatedTypeFormatter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotationClassLoader;
import org.checkerframework.framework.type.DefaultAnnotatedTypeFormatter;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.AnnotationFormatter;
import org.checkerframework.framework.util.GraphQualifierHierarchy;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ErrorReporter;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import units.qual.IsBaseUnit;
import units.qual.PolyUnit;
import units.qual.UnitsAlias;
import units.qual.UnitsInternal;
import units.representation.UnitsRepresentationUtils;
import units.util.UnitsTypecheckUtils;

public class UnitsAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {
    // protected final AnnotationMirror TOP =
    // AnnotationBuilder.fromClass(elements, UnknownUnits.class);
    // protected final AnnotationMirror BOTTOM =
    // AnnotationBuilder.fromClass(elements, UnitsBottom.class);

    // static reference to the singleton instance
    protected static UnitsRepresentationUtils unitsRepresentationUtils;

    public UnitsAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        unitsRepresentationUtils = UnitsRepresentationUtils.getInstance(processingEnv, elements);
        postInit();
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
        unitsRepresentationUtils.postInit();

        return qualSet;
    }

    @Override
    public AnnotationMirror aliasedAnnotation(AnnotationMirror anno) {

//        if (anno.toString().startsWith("@units.qual.")) {
//            System.out.println(" === checking alias unit for " + anno.toString());
//        }

        // check to see if it is an internal units annotation
        if (AnnotationUtils.areSameByClass(anno, UnitsInternal.class)) {
            // fill in missing base units
            return unitsRepresentationUtils.fillMissingBaseUnits(anno);
        }

        // check to see if it's a surface annotation such as @m or @UnknownUnits
        for (AnnotationMirror metaAnno : anno.getAnnotationType().asElement()
                .getAnnotationMirrors()) {

            // if it has a UnitsAlias or IsBaseUnit meta-annotation, then it must have been prebuilt
            // return the prebuilt internal annotation
            if (AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)
                    || AnnotationUtils.areSameByClass(metaAnno, IsBaseUnit.class)) {

               //  System.out.println("     returning prebuilt alias for " + anno.toString());

                return unitsRepresentationUtils.getInternalAliasUnit(anno);
            }

            //
            // // Check to see if it is an alias unit
            // if (AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)) {
            // Map<String, Integer> exponents = new TreeMap<>();
            //
            // int prefix = 0;
            // // default all base units to exponent 0
            // for (String bu : unitsRepresentationUtils.baseUnits()) {
            // exponents.put(bu, 0);
            // }
            // // replace default base unit exponents from anno
            // for (AnnotationMirror bu : AnnotationUtils.getElementValueArray(metaAnno, "value",
            // AnnotationMirror.class, true)) {
            // exponents.put(AnnotationUtils.getElementValue(bu, "unit", String.class, false),
            // AnnotationUtils.getElementValue(bu, "exponent", Integer.class, true));
            // prefix += AnnotationUtils.getElementValue(bu, "prefix", Integer.class, true);
            // }
            //
            // return unitsRepresentationUtils.addUnitsAnnotation(anno, "", false, false, prefix,
            // exponents);
            // }
        }
        
        return super.aliasedAnnotation(anno);
    }

    // programmatically set the defaults
    @Override
    protected void addCheckedCodeDefaults(QualifierDefaults defs) {
        // set DIMENSIONLESS as the default qualifier in hierarchy
        defs.addCheckedCodeDefault(unitsRepresentationUtils.DIMENSIONLESS,
                TypeUseLocation.OTHERWISE);
        defs.addCheckedCodeDefault(unitsRepresentationUtils.TOP,
                TypeUseLocation.IMPLICIT_UPPER_BOUND);
        defs.addCheckedCodeDefault(unitsRepresentationUtils.BOTTOM, TypeUseLocation.LOWER_BOUND);
    }

    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new UnitsQualifierHierarchy(factory);
    }

    private final class UnitsQualifierHierarchy extends GraphQualifierHierarchy {
        public UnitsQualifierHierarchy(MultiGraphFactory mgf) {
            super(mgf, unitsRepresentationUtils.BOTTOM);
        }

        // Programmatically set UnitsRepresentationUtils.BOTTOM as the bottom
        @Override
        protected Set<AnnotationMirror> findBottoms(
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypes) {
            Set<AnnotationMirror> newBottoms = super.findBottoms(supertypes);

            newBottoms.remove(unitsRepresentationUtils.RAWUNITSINTERNAL);
            newBottoms.add(unitsRepresentationUtils.BOTTOM);

            // set direct supertypes of bottom
            Set<AnnotationMirror> supertypesOfBottom = new LinkedHashSet<>();
            supertypesOfBottom.add(unitsRepresentationUtils.TOP);
            supertypes.put(unitsRepresentationUtils.BOTTOM, supertypesOfBottom);

            return newBottoms;
        }

        // Programmatically set UnitsRepresentationUtils.TOP as the top
        @Override
        protected void finish(QualifierHierarchy qualHierarchy,
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypes,
                Map<AnnotationMirror, AnnotationMirror> polyQualifiers, Set<AnnotationMirror> tops,
                Set<AnnotationMirror> bottoms, Object... args) {
            super.finish(qualHierarchy, supertypes, polyQualifiers, tops, bottoms, args);

            assert supertypes.containsKey(unitsRepresentationUtils.RAWUNITSINTERNAL);
            // Set direct supertypes of TOP
            supertypes.put(unitsRepresentationUtils.TOP,
                    supertypes.get(unitsRepresentationUtils.RAWUNITSINTERNAL));
            supertypes.remove(unitsRepresentationUtils.RAWUNITSINTERNAL);

            // update tops
            tops.remove(unitsRepresentationUtils.RAWUNITSINTERNAL);
            tops.add(unitsRepresentationUtils.TOP);

            System.out.println(" === supertypes: " + supertypes);
            System.out.println(" === polyQualifiers: " + polyQualifiers);
            System.out.println(" === tops: " + tops);
            System.out.println(" === bottoms: " + bottoms);
        }

        @Override
        public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
            // // replace UnknownUnits and UnitsBottom with internal versions
            // if (AnnotationUtils.areSame(subAnno, TOP)) {
            // subAnno = UnitsRepresentationUtils.TOP;
            // } else if (AnnotationUtils.areSame(subAnno, BOTTOM)) {
            // subAnno = UnitsRepresentationUtils.BOTTOM;
            // }
            // if (AnnotationUtils.areSame(superAnno, TOP)) {
            // superAnno = UnitsRepresentationUtils.TOP;
            // } else if (AnnotationUtils.areSame(superAnno, BOTTOM)) {
            // superAnno = UnitsRepresentationUtils.BOTTOM;
            // }

            // System.out.println(" === checking SUBTYPE " + subAnno + " <: " + superAnno);

            // replace raw UnitsInternal with Dimensionless
            // for some reason this shows up in inference mode when building the lattice
            if (AnnotationUtils.areSameByClass(subAnno, UnitsInternal.class)) {
                subAnno = unitsRepresentationUtils.DIMENSIONLESS;
            }
            if (AnnotationUtils.areSameByClass(superAnno, UnitsInternal.class)) {
                superAnno = unitsRepresentationUtils.DIMENSIONLESS;
            }

            // Case: @UnitsInternal <: Top
            if (AnnotationUtils.areSame(superAnno, unitsRepresentationUtils.TOP)) {
                return true;
            }

            // Case: Bottom <: @UnitsInternal
            if (AnnotationUtils.areSame(subAnno, unitsRepresentationUtils.BOTTOM)) {
                return true;
            }

            // Case: @PolyAll <: All units
            // Case: @PolyUnit <: PolyAll and All units
            if (AnnotationUtils.areSameByClass(subAnno, PolyAll.class)
                    || AnnotationUtils.areSameByClass(subAnno, PolyUnit.class)) {
                return true;
            }

            // Case: Any unit except Top <: PolyAll or PolyUnit
            if (!AnnotationUtils.areSame(subAnno, unitsRepresentationUtils.TOP)
                    && (AnnotationUtils.areSameByClass(superAnno, PolyAll.class)
                            || AnnotationUtils.areSameByClass(superAnno, PolyUnit.class))) {
                return true;
            }

            // Case: @UnitsInternal(x) <: @UnitsInternal(y)
            if (AnnotationUtils.areSameByClass(subAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameByClass(superAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameIgnoringValues(subAnno, superAnno)) {
                return UnitsTypecheckUtils.unitsEqual(subAnno, superAnno);
            }

            ErrorReporter.errorAbort("Uncaught subtype check case:" + "\n    subtype:   " + subAnno
                    + "\n    supertype: " + superAnno);

            // // Case X <: Y
            // Set<AnnotationMirror> supermap1 = this.supertypesMap.get(subAnno);
            // return AnnotationUtils.containsSame(supermap1, superAnno);

            // // remove values inside UnitsInternal for any other subtype checks, via super
            // if (AnnotationUtils.areSameByClass(subAnno, UnitsInternal.class)) {
            // subAnno = unitsRepresentationUtils.RAWUNITSINTERNAL;
            // } else if (AnnotationUtils.areSameByClass(superAnno, UnitsInternal.class)) {
            // superAnno = unitsRepresentationUtils.RAWUNITSINTERNAL;
            // }
            return super.isSubtype(subAnno, superAnno);
        }
    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(new UnitsPropagationTreeAnnotator(),
                new ImplicitsTreeAnnotator(this));
    }

    public class UnitsPropagationTreeAnnotator extends PropagationTreeAnnotator {
        public UnitsPropagationTreeAnnotator() {
            super(UnitsAnnotatedTypeFactory.this);
        }

        @Override
        public Void visitBinary(BinaryTree node, AnnotatedTypeMirror type) {
            Kind kind = node.getKind();
            AnnotationMirror lhsAM = atypeFactory.getAnnotatedType(node.getLeftOperand())
                    .getEffectiveAnnotationInHierarchy(unitsRepresentationUtils.RAWUNITSINTERNAL);
            AnnotationMirror rhsAM = atypeFactory.getAnnotatedType(node.getRightOperand())
                    .getEffectiveAnnotationInHierarchy(unitsRepresentationUtils.RAWUNITSINTERNAL);

            switch (kind) {
                case PLUS:
                    if (AnnotationUtils.areSame(lhsAM, rhsAM)) {
                        type.replaceAnnotation(lhsAM);
                    }
                    break;
                case MINUS:
                    if (AnnotationUtils.areSame(lhsAM, rhsAM)) {
                        type.replaceAnnotation(lhsAM);
                    }
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
                default:
                    // Check LUB by default
                    return super.visitBinary(node, type);
            }

            return null;
        }
    }

    // for use in AnnotatedTypeMirror.toString()
    @Override
    protected AnnotatedTypeFormatter createAnnotatedTypeFormatter() {
        return new DefaultAnnotatedTypeFormatter(createAnnotationFormatter(),
                checker.hasOption("printVerboseGenerics"), checker.hasOption("printAllQualifiers"));
    }

    // for use in generating error outputs
    @Override
    protected AnnotationFormatter createAnnotationFormatter() {
        return new UnitsAnnotationFormatter(checker);
    }
}
