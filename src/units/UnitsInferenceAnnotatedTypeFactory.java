package units;

import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationBuilder;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.LiteralTree;
import checkers.inference.InferenceAnnotatedTypeFactory;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceQualifierHierarchy;
import checkers.inference.InferenceTreeAnnotator;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import units.qual.Dimensionless;
import units.qual.UnitsBottom;
import units.qual.UnknownUnits;
import units.qual.m;
import units.qual.s;

public class UnitsInferenceAnnotatedTypeFactory extends InferenceAnnotatedTypeFactory {

    protected final AnnotationMirror UNKNOWNUNITS =
            AnnotationBuilder.fromClass(elements, UnknownUnits.class);
    protected final AnnotationMirror BOTTOM =
            AnnotationBuilder.fromClass(elements, UnitsBottom.class);

    protected final AnnotationMirror DIMENSIONLESS =
            AnnotationBuilder.fromClass(elements, Dimensionless.class);
    protected final AnnotationMirror METER = AnnotationBuilder.fromClass(elements, m.class);
    protected final AnnotationMirror SECOND = AnnotationBuilder.fromClass(elements, s.class);

    public UnitsInferenceAnnotatedTypeFactory(InferenceChecker inferenceChecker,
            boolean withCombineConstraints, BaseAnnotatedTypeFactory realTypeFactory,
            InferrableChecker realChecker, SlotManager slotManager,
            ConstraintManager constraintManager) {
        super(inferenceChecker, withCombineConstraints, realTypeFactory, realChecker, slotManager,
                constraintManager);
        postInit();
    }

    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new UnitsInferenceQualifierHierarchy(factory);
    }

    private final class UnitsInferenceQualifierHierarchy extends InferenceQualifierHierarchy {

        public UnitsInferenceQualifierHierarchy(MultiGraphFactory multiGraphFactory) {
            super(multiGraphFactory);
        }

        // @Override
        // protected Set<AnnotationMirror> findBottoms(
        // Map<AnnotationMirror, Set<AnnotationMirror>> supertypes) {
        // Set<AnnotationMirror> newBottoms = super.findBottoms(supertypes);
        // newBottoms.remove(UnitsUtils.ONTOLOGY);
        // newBottoms.add(UnitsUtils.ONTOLOGY_BOTTOM);
        //
        // //update supertypes
        // Set<AnnotationMirror> supertypesOfBtm = new HashSet<>();
        // supertypesOfBtm.add(UnitsUtils.ONTOLOGY_TOP);
        // supertypes.put(UnitsUtils.ONTOLOGY_BOTTOM, supertypesOfBtm);
        //
        // return newBottoms;
        // }

        // @Override
        // protected void finish(
        // QualifierHierarchy qualHierarchy,
        // Map<AnnotationMirror, Set<AnnotationMirror>> fullMap,
        // Map<AnnotationMirror, AnnotationMirror> polyQualifiers,
        // Set<AnnotationMirror> tops,
        // Set<AnnotationMirror> bottoms,
        // Object... args) {
        // super.finish(qualHierarchy, fullMap, polyQualifiers, tops, bottoms, args);
        //
        // // substitue ONTOLOGY with ONTOLOGY_TOP in fullMap
        // assert fullMap.containsKey(UnitsUtils.ONTOLOGY);
        // Set<AnnotationMirror> ontologyTopSupers = fullMap.get(UnitsUtils.ONTOLOGY);
        // fullMap.put(UnitsUtils.ONTOLOGY_TOP, ontologyTopSupers);
        // fullMap.remove(UnitsUtils.ONTOLOGY);
        // }
    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(
                new UnitsInferenceTreeAnnotator(
                        this, realChecker, realTypeFactory, variableAnnotator, slotManager),
                new ImplicitsTreeAnnotator(this));
    }

    public class UnitsInferenceTreeAnnotator extends InferenceTreeAnnotator {

        private final VariableAnnotator variableAnnotator;

        public UnitsInferenceTreeAnnotator(InferenceAnnotatedTypeFactory atypeFactory,
                InferrableChecker realChecker, AnnotatedTypeFactory realAnnotatedTypeFactory,
                VariableAnnotator variableAnnotator, SlotManager slotManager) {
            super(atypeFactory, realChecker, realAnnotatedTypeFactory, variableAnnotator,
                    slotManager);
            this.variableAnnotator = variableAnnotator;
        }

        @Override
        public Void visitLiteral(LiteralTree literalTree, AnnotatedTypeMirror atm) {
            // TODO: refine it down to number literals

            // number literals are always dimensionless

            // Create an AM
            AnnotationMirror anno = DIMENSIONLESS; // Default for all literals
            // Create a slot
            ConstantSlot cs = variableAnnotator.createConstant(anno, literalTree);
            // Replace atm value
            atm.replaceAnnotation(cs.getValue());
            // Visit the atm with the tree
            variableAnnotator.visit(atm, literalTree);
            return null;
        }

        @Override
        public Void visitBinary(BinaryTree node, AnnotatedTypeMirror type) {
            // // Overrides only required if i want to replace a varslot iwth constant slot
            // // varAnnotator adds varSlots, call it sometimes, see InfTreeANnotator
            //
            // // Create an AM
            // AnnotationMirror anno = METER; // TODO
            // // Create a slot
            // ConstantSlot cs = variableAnnotator.createConstant(anno, node);
            // // Replace atm value
            // type.replaceAnnotation(cs.getValue());
            // // Visit the atm with the tree
            // variableAnnotator.visit(type, node);
            //
            // return null;
            return super.visitBinary(node, type);
        }

        // @Override
        // public Void visitNewClass(final NewClassTree newClassTree, final AnnotatedTypeMirror atm)
        // {
        // switch (UnitsUtils.determineUnitsValue(atm.getUnderlyingType())) {
        // case SEQUENCE: {
        // AnnotationMirror anno = UnitsUtils.createUnitsAnnotationByValues(processingEnv,
        // UnitsValue.SEQUENCE);
        // ConstantSlot cs = variableAnnotator.createConstant(anno, newClassTree);
        // atm.replaceAnnotation(cs.getValue());
        // }
        // break;
        //
        // case TOP:
        // default:
        // break;
        // }
        // variableAnnotator.visit(atm, newClassTree.getIdentifier());
        // return null;
        // }
        //
        // @Override
        // public Void visitNewArray(final NewArrayTree newArrayTree, final AnnotatedTypeMirror atm)
        // {
        // AnnotationMirror anno =
        // UnitsUtils.createUnitsAnnotationByValues(processingEnv, UnitsValue.SEQUENCE);
        // ConstantSlot cs = variableAnnotator.createConstant(anno, newArrayTree);
        // atm.replaceAnnotation(cs.getValue());
        // variableAnnotator.visit(atm, newArrayTree);
        // return null;
        // }
        //
        // @Override
        // public Void visitParameterizedType(final ParameterizedTypeTree param,
        // final AnnotatedTypeMirror atm) {
        // TreePath path = atypeFactory.getPath(param);
        // if (path != null) {
        // final TreePath parentPath = path.getParentPath();
        // final Tree parentNode = parentPath.getLeaf();
        // if (!parentNode.getKind().equals(Kind.NEW_CLASS)) {
        // variableAnnotator.visit(atm, param);
        // }
        // }
        // return null;
        // }
    }
}
