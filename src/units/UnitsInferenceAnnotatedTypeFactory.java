package units;

import java.lang.annotation.Annotation;
import java.util.HashSet;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.Pair;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.VariableTree;
import checkers.inference.InferenceAnnotatedTypeFactory;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceQualifierHierarchy;
import checkers.inference.InferenceTreeAnnotator;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import units.util.UnitsUtils;

public class UnitsInferenceAnnotatedTypeFactory extends InferenceAnnotatedTypeFactory {

    public UnitsInferenceAnnotatedTypeFactory(InferenceChecker inferenceChecker,
            BaseAnnotatedTypeFactory realTypeFactory, InferrableChecker realChecker,
            SlotManager slotManager, ConstraintManager constraintManager) {
        super(inferenceChecker, false, realTypeFactory, realChecker, slotManager,
                constraintManager);
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
        // for (AnnotationMirror metaAnno : anno.getAnnotationType().asElement()
        // .getAnnotationMirrors()) {
        // if (AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)) {
        //
        // System.out.println(" aliasing " + anno);
        //
        // Map<String, Integer> exponents = new TreeMap<>();
        // exponents.put("m", 1);
        // exponents.put("s", 1);
        //
        // return UnitsUtils.createInternalUnit("dummy", 1, exponents);
        // }
        // }

        return super.aliasedAnnotation(anno);
    }

    @Override
    public VariableAnnotator createVariableAnnotator() {
        return new UnitsVariableAnnotator(
                this, realTypeFactory, realChecker, slotManager, constraintManager);
    }

    private final class UnitsVariableAnnotator extends VariableAnnotator {

        public UnitsVariableAnnotator(InferenceAnnotatedTypeFactory typeFactory,
                AnnotatedTypeFactory realTypeFactory, InferrableChecker realChecker,
                SlotManager slotManager, ConstraintManager constraintManager) {
            super(typeFactory, realTypeFactory, realChecker, slotManager, constraintManager);
        }

        @Override
        public void handleBinaryTree(AnnotatedTypeMirror atm, BinaryTree binaryTree) {
            // Identical to super implementation except that we don't create a LUB constraint here
            // by default.
            if (treeToVarAnnoPair.containsKey(binaryTree)) {
                atm.replaceAnnotations(treeToVarAnnoPair.get(binaryTree).second);
            } else {
                AnnotatedTypeMirror a =
                        inferenceTypeFactory.getAnnotatedType(binaryTree.getLeftOperand());
                AnnotatedTypeMirror b =
                        inferenceTypeFactory.getAnnotatedType(binaryTree.getRightOperand());
                Set<? extends AnnotationMirror> lubs = inferenceTypeFactory.getQualifierHierarchy()
                        .leastUpperBounds(a.getEffectiveAnnotations(), b.getEffectiveAnnotations());
                atm.clearAnnotations();
                atm.addAnnotations(lubs);
                if (slotManager.getVariableSlot(atm).isVariable()) {
                    final Pair<VariableSlot, Set<? extends AnnotationMirror>> varATMPair =
                            Pair.<VariableSlot, Set<? extends AnnotationMirror>>of(
                                    slotManager.getVariableSlot(atm), lubs);
                    treeToVarAnnoPair.put(binaryTree, varATMPair);
                } else {
                    // The slot returned was a constant. Regenerating it is ok.
                }
            }
        }
    }

    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new UnitsInferenceQualifierHierarchy(factory);
    }

    private final class UnitsInferenceQualifierHierarchy extends InferenceQualifierHierarchy {

        public UnitsInferenceQualifierHierarchy(MultiGraphFactory multiGraphFactory) {
            super(multiGraphFactory);
        }

    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        UnitsUtils.getInstance(processingEnv, elements);
        return new ListTreeAnnotator(
                new ImplicitsTreeAnnotator(this), new UnitsInferenceTreeAnnotator(
                        this, realChecker, realTypeFactory, variableAnnotator, slotManager));
    }

    public class UnitsInferenceTreeAnnotator extends InferenceTreeAnnotator {

        public UnitsInferenceTreeAnnotator(InferenceAnnotatedTypeFactory atypeFactory,
                InferrableChecker realChecker, AnnotatedTypeFactory realAnnotatedTypeFactory,
                VariableAnnotator variableAnnotator, SlotManager slotManager) {
            super(atypeFactory, realChecker, realAnnotatedTypeFactory, variableAnnotator,
                    slotManager);
        }

        @Override
        public Void visitVariable(VariableTree varTree, AnnotatedTypeMirror atm) {
            // Use super to create a varAnnot for the variable declaration
            super.visitVariable(varTree, atm);

            // Add an equality constraint between the varAnnot and the type qualifier
            // declared on the variable (or default type qualifier)
            AnnotatedTypeMirror realATM = realTypeFactory.getAnnotatedType(varTree);
            AnnotationMirror realAnno = realATM.getAnnotationInHierarchy(UnitsUtils.UNKNOWNUNITS);
            ConstantSlot declaredAnnoSlot = variableAnnotator.createConstant(realAnno, varTree);
            Slot varAnnotSlot = slotManager.getSlot(atm.getAnnotationInHierarchy(getVarAnnot()));
            constraintManager.addEqualityConstraint(varAnnotSlot, declaredAnnoSlot);

            return null;
        }

        @Override
        public Void visitLiteral(LiteralTree literalTree, AnnotatedTypeMirror atm) {
            // get the default type for literals
            AnnotatedTypeMirror realATM = realTypeFactory.getAnnotatedType(literalTree);
            AnnotationMirror realAnno = realATM.getAnnotationInHierarchy(UnitsUtils.UNKNOWNUNITS);
            ConstantSlot cs = variableAnnotator.createConstant(realAnno, literalTree);
            atm.replaceAnnotation(cs.getValue());
            variableAnnotator.visit(atm, literalTree);
            return null;
        }

        @Override
        public Void visitBinary(BinaryTree binaryTree, AnnotatedTypeMirror atm) {
            Kind kind = binaryTree.getKind();
            switch (kind) {
                case PLUS:
                    // visit to create a varslot for the result atm
                    variableAnnotator.visit(atm, binaryTree);
                    addArithmeticConstraint(kind, binaryTree, atm);
                    return null;
                default:
                    return super.visitBinary(binaryTree, atm);
            }

            // Map<String, Integer> exponents = new TreeMap<>();
            // exponents.put("m", 1);
            // exponents.put("s", 1);
            //
            // AnnotationMirror anno = UnitsUtils.createInternalUnit("dummy", 1, exponents);
            // ConstantSlot cs = variableAnnotator.createConstant(anno, binaryTree);
            // atm.replaceAnnotation(cs.getValue());
            // variableAnnotator.visit(atm, binaryTree);
        }

        private void addArithmeticConstraint(Kind kind, BinaryTree binaryTree,
                AnnotatedTypeMirror atm) {
            AnnotatedTypeMirror lhsATM = atypeFactory.getAnnotatedType(binaryTree.getLeftOperand());
            AnnotatedTypeMirror rhsATM =
                    atypeFactory.getAnnotatedType(binaryTree.getRightOperand());

            Slot lhs = slotManager.getVariableSlot(lhsATM);
            Slot rhs = slotManager.getVariableSlot(rhsATM);
            Slot result = slotManager.getVariableSlot(atm);

            if (binaryTree.getKind() == Kind.PLUS) {
                constraintManager.addAdditionConstraint(lhs, rhs, result);
            }
        }

    }
}
