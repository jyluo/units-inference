package units;

import java.lang.annotation.Annotation;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
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
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import units.otherquals.IsBaseUnit;
import units.otherquals.UnitsAlias;
import units.qual.UnitsInternal;
import units.representation.UnitsRepresentationUtils;
import units.util.UnitsTypecheckUtils;

public class UnitsAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {
    // protected final AnnotationMirror UNKNOWNUNITS =
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
        for (AnnotationMirror metaAnno : anno.getAnnotationType().asElement()
                .getAnnotationMirrors()) {

            // Check to see if it is an alias unit
            if (AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)) {
                Map<String, Integer> exponents = new TreeMap<>();

                int prefix = 0;
                // default all base units to exponent 0
                for (String bu : unitsRepresentationUtils.baseUnits()) {
                    exponents.put(bu, 0);
                }
                // replace default base unit exponents from anno
                for (AnnotationMirror bu : AnnotationUtils.getElementValueArray(metaAnno, "value",
                        AnnotationMirror.class, true)) {
                    exponents.put(AnnotationUtils.getElementValue(bu, "unit", String.class, false),
                            AnnotationUtils.getElementValue(bu, "exponent", Integer.class, true));
                    prefix += AnnotationUtils.getElementValue(bu, "prefix", Integer.class, true);
                }

                unitsRepresentationUtils.addUnitsAnnotation(anno);
                return unitsRepresentationUtils.createInternalUnit("", false, false, prefix,
                        exponents);
            }

            // Check to see if it declares a base unit
            if (AnnotationUtils.areSameByClass(metaAnno, IsBaseUnit.class)) {
                Map<String, Integer> exponents = new TreeMap<>();
                // default all base units to exponent 0
                for (String bu : unitsRepresentationUtils.baseUnits()) {
                    exponents.put(bu, 0);
                }
                exponents.put(anno.getAnnotationType().asElement().getSimpleName().toString(), 1);

                unitsRepresentationUtils.addUnitsAnnotation(anno);
                return unitsRepresentationUtils.createInternalUnit("", false, false, 0, exponents);
            }
        }

        return super.aliasedAnnotation(anno);
    }

    // programmatically set the defaults
    @Override
    protected void addCheckedCodeDefaults(QualifierDefaults defs) {
        // set DIMENSIONLESS as the default qualifier in hierarchy
        defs.addCheckedCodeDefault(unitsRepresentationUtils.DIMENSIONLESS,
                TypeUseLocation.OTHERWISE);
        defs.addCheckedCodeDefault(unitsRepresentationUtils.UNKNOWNUNITS,
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
            supertypesOfBottom.add(unitsRepresentationUtils.RAWUNITSINTERNAL);
            supertypes.put(unitsRepresentationUtils.BOTTOM, supertypesOfBottom);

            return newBottoms;
        }

        // Programmatically set UnitsRepresentationUtils.UNKNOWNUNITS as the top
        @Override
        protected void finish(QualifierHierarchy qualHierarchy,
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypes,
                Map<AnnotationMirror, AnnotationMirror> polyQualifiers, Set<AnnotationMirror> tops,
                Set<AnnotationMirror> bottoms, Object... args) {
            super.finish(qualHierarchy, supertypes, polyQualifiers, tops, bottoms, args);

            assert supertypes.containsKey(unitsRepresentationUtils.RAWUNITSINTERNAL);
            assert supertypes.get(unitsRepresentationUtils.RAWUNITSINTERNAL).size() == 0;
            // Set direct supertypes of UNKNOWNUNITS
            supertypes.put(unitsRepresentationUtils.UNKNOWNUNITS, Collections.emptySet());

            // update direct supertypes of RAWUNITSINTERNAL
            Set<AnnotationMirror> supertypesOfRawUnitsInternal = new HashSet<>();
            supertypesOfRawUnitsInternal.add(unitsRepresentationUtils.UNKNOWNUNITS);
            supertypes.put(unitsRepresentationUtils.RAWUNITSINTERNAL,
                    Collections.unmodifiableSet(supertypesOfRawUnitsInternal));

            // update tops
            tops.remove(unitsRepresentationUtils.RAWUNITSINTERNAL);
            tops.add(unitsRepresentationUtils.UNKNOWNUNITS);
        }

        @Override
        public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
            // // replace UnknownUnits and UnitsBottom with internal versions
            // if (AnnotationUtils.areSame(subAnno, UNKNOWNUNITS)) {
            // subAnno = UnitsRepresentationUtils.UNKNOWNUNITS;
            // } else if (AnnotationUtils.areSame(subAnno, BOTTOM)) {
            // subAnno = UnitsRepresentationUtils.BOTTOM;
            // }
            // if (AnnotationUtils.areSame(superAnno, UNKNOWNUNITS)) {
            // superAnno = UnitsRepresentationUtils.UNKNOWNUNITS;
            // } else if (AnnotationUtils.areSame(superAnno, BOTTOM)) {
            // superAnno = UnitsRepresentationUtils.BOTTOM;
            // }

            // Case: @UnitsInternal <: Top
            if (AnnotationUtils.areSame(superAnno, unitsRepresentationUtils.UNKNOWNUNITS)) {
                return true;
            }

            // Case: Bottom <: @UnitsInternal
            if (AnnotationUtils.areSame(subAnno, unitsRepresentationUtils.BOTTOM)) {
                return true;
            }

            // Case: @UnitsInternal(x) <: @UnitsInternal(y)
            if (AnnotationUtils.areSameByClass(subAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameByClass(superAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameIgnoringValues(subAnno, superAnno)) {
                return UnitsTypecheckUtils.unitsEqual(subAnno, superAnno);
            }

            // remove values inside UnitsInternal for any other subtype checks, via super
            if (AnnotationUtils.areSameByClass(subAnno, UnitsInternal.class)) {
                subAnno = unitsRepresentationUtils.RAWUNITSINTERNAL;
            } else if (AnnotationUtils.areSameByClass(superAnno, UnitsInternal.class)) {
                superAnno = unitsRepresentationUtils.RAWUNITSINTERNAL;
            }
            System.out.println(" CHECKING SUBTYPE " + subAnno + " <: " + superAnno);
            return super.isSubtype(subAnno, superAnno);
        }
    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(
                new UnitsPropagationTreeAnnotator(), new ImplicitsTreeAnnotator(this));
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
