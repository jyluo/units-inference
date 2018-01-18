package units;

import java.lang.annotation.Annotation;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.GraphQualifierHierarchy;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import units.qual.IsBaseUnit;
import units.qual.UnitsAlias;
import units.qual.UnitsBottom;
import units.qual.UnitsInternal;
import units.qual.UnknownUnits;
import units.util.UnitsTypecheckUtils;
import units.util.UnitsUtils;

public class UnitsAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {

    protected final AnnotationMirror UNKNOWNUNITS =
            AnnotationBuilder.fromClass(elements, UnknownUnits.class);
    protected final AnnotationMirror BOTTOM =
            AnnotationBuilder.fromClass(elements, UnitsBottom.class);

    public UnitsAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        UnitsUtils.getInstance(processingEnv, elements);
        postInit();
    }

    @Override
    protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
        // Use the Units Annotated Type Loader instead of the default one
        loader = new UnitsAnnotationClassLoader(checker);

        // get all the loaded annotations
        Set<Class<? extends Annotation>> qualSet = new HashSet<Class<? extends Annotation>>();
        qualSet.addAll(getBundledTypeQualifiersWithPolyAll());

        // // load all the external units
        // loadAllExternalUnits();
        //
        // // copy all loaded external Units to qual set
        // qualSet.addAll(externalQualsMap.values());

        return qualSet;
    }

    @Override
    public AnnotationMirror aliasedAnnotation(AnnotationMirror anno) {
        for (AnnotationMirror metaAnno : anno.getAnnotationType().asElement()
                .getAnnotationMirrors()) {
            if (AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)) {
                Map<String, Integer> exponents = new TreeMap<>();

                int prefix = 0;
                // default all base units to exponent 0
                for (String bu : UnitsUtils.baseUnits()) {
                    exponents.put(bu, 0);
                }
                // replace default base unit exponents from anno
                for (AnnotationMirror bu : AnnotationUtils.getElementValueArray(metaAnno, "value",
                        AnnotationMirror.class, true)) {
                    exponents.put(AnnotationUtils.getElementValue(bu, "unit", String.class, false),
                            AnnotationUtils.getElementValue(bu, "exponent", Integer.class, true));
                    prefix += AnnotationUtils.getElementValue(bu, "prefix", Integer.class, true);
                }

                UnitsUtils.addUnitsAnnotation(anno);
                return UnitsUtils.createInternalUnit("", false, false, prefix, exponents);
            }

            if (AnnotationUtils.areSameByClass(metaAnno, IsBaseUnit.class)) {
                Map<String, Integer> exponents = new TreeMap<>();
                // default all base units to exponent 0
                for (String bu : UnitsUtils.baseUnits()) {
                    exponents.put(bu, 0);
                }
                exponents.put(anno.getAnnotationType().asElement().getSimpleName().toString(), 1);

                UnitsUtils.addUnitsAnnotation(anno);
                return UnitsUtils.createInternalUnit("", false, false, 0, exponents);
            }
        }

        return super.aliasedAnnotation(anno);
    }

    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new UnitsQualifierHierarchy(factory, BOTTOM);
    }

    private final class UnitsQualifierHierarchy extends GraphQualifierHierarchy {

        public UnitsQualifierHierarchy(MultiGraphFactory mgf, AnnotationMirror bottom) {
            super(mgf, bottom);
        }

        @Override
        public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
            // Case: @UnitsInternal <: Top
            if (AnnotationUtils.areSame(superAnno, UnitsUtils.UNKNOWNUNITS)) {
                return true;
            }

            // Case: Bottom <: @UnitsInternal
            if (AnnotationUtils.areSame(subAnno, UnitsUtils.BOTTOM)) {
                return true;
            }

            // Case: @UnitsInternal(x) <: @UnitsInternal(y)
            if (AnnotationUtils.areSameByClass(subAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameByClass(superAnno, UnitsInternal.class)
                    && AnnotationUtils.areSameIgnoringValues(subAnno, superAnno)) {
                return UnitsTypecheckUtils.unitsEqual(subAnno, superAnno);
            }

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
                    .getEffectiveAnnotationInHierarchy(UNKNOWNUNITS);
            AnnotationMirror rhsAM = atypeFactory.getAnnotatedType(node.getRightOperand())
                    .getEffectiveAnnotationInHierarchy(UNKNOWNUNITS);

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
}
