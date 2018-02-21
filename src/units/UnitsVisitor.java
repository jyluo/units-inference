package units;

import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceMain;
import checkers.inference.InferenceVisitor;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.VariableSlot;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;

public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {

    protected final SlotManager slotManager;
    protected final ConstraintManager constraintManager;

    public UnitsVisitor(UnitsChecker checker, InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory, boolean infer) {
        super(checker, ichecker, factory, infer);
        constraintManager = InferenceMain.getInstance().getConstraintManager();
        slotManager = InferenceMain.getInstance().getSlotManager();
    }

    @Override
    public Void visitBinary(BinaryTree node, Void p) {
        if (infer) {
            AnnotatedTypeMirror lhsATM = atypeFactory.getAnnotatedType(node.getLeftOperand());
            AnnotatedTypeMirror rhsATM = atypeFactory.getAnnotatedType(node.getRightOperand());
            VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
            VariableSlot rhs = slotManager.getVariableSlot(rhsATM);
            switch (node.getKind()) {
                case PLUS:
                case MINUS:
                case MULTIPLY:
                case DIVIDE:
                case REMAINDER:
                    // use "create" to grab the already created slot
                    ArithmeticVariableSlot result = slotManager.createArithmeticVariableSlot(
                            VariableAnnotator.treeToLocation(atypeFactory, node));
                    constraintManager.addArithmeticConstraint(
                            ArithmeticOperationKind.fromTreeKind(node.getKind()), lhs, rhs, result);
                default:
                    // TODO: replace with LUBSlot pending mier's PR
                    VariableSlot lubSlot = slotManager.createCombVariableSlot(lhs, rhs);
                    // Create LUB constraint by default
                    constraintManager.addSubtypeConstraint(lhs, lubSlot);
                    constraintManager.addSubtypeConstraint(rhs, lubSlot);
            }

        } else { // if (atypeFactory instanceof UnitsAnnotatedTypeFactory)
            UnitsAnnotatedTypeFactory atf = (UnitsAnnotatedTypeFactory) atypeFactory;

            Kind kind = node.getKind();
            AnnotationMirror lhsAM = atf.getAnnotatedType(node.getLeftOperand())
                    .getEffectiveAnnotationInHierarchy(atf.UNKNOWNUNITS);
            AnnotationMirror rhsAM = atf.getAnnotatedType(node.getRightOperand())
                    .getEffectiveAnnotationInHierarchy(atf.UNKNOWNUNITS);

            switch (kind) {
                case PLUS:
                    if (!AnnotationUtils.areSame(lhsAM, rhsAM)) {
                        checker.report(Result.failure("addition.unit.mismatch", lhsAM.toString(),
                                rhsAM.toString()), node);
                    }
                    break;
                case MINUS:
                    if (!AnnotationUtils.areSame(lhsAM, rhsAM)) {
                        checker.report(Result.failure("subtraction.unit.mismatch", lhsAM.toString(),
                                rhsAM.toString()), node);
                    }
                    break;
                default:
                    break;
            }
        }

        return super.visitBinary(node, p);
    }

    // @Override
    // public Void visitVariable(VariableTree node, Void p) {
    // System.out.println(" UnitsVisitor visitVariable: " + node);
    // return super.visitVariable(node, p);
    // }
    //
    // @Override
    // public Void visitAssignment(AssignmentTree node, Void p) {
    // System.out.println(" UnitsVisitor visitAssignment: " + node);
    // return super.visitAssignment(node, p);
    // }

    // Slots created in ATF

    // Constraints created in Visitor

    // see
    // https://github.com/topnessman/immutability/blob/master/src/main/java/pico/inference/PICOInferenceVisitor.java


}
