package units;

import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceMain;
import checkers.inference.InferenceVisitor;
import checkers.inference.SlotManager;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.VariableSlot;
import units.representation.UnitsRepresentationUtils;

public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {

    public UnitsVisitor(UnitsChecker checker, InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory, boolean infer) {
        super(checker, ichecker, factory, infer);
    }

    @Override
    protected void commonAssignmentCheck(AnnotatedTypeMirror varType, AnnotatedTypeMirror valueType,
            Tree valueTree, String errorKey) {
        super.commonAssignmentCheck(varType, valueType, valueTree, errorKey);
    }

    @Override
    public Void visitBinary(BinaryTree node, Void p) {
        if (infer) {
            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
            ConstraintManager constraintManager =
                    InferenceMain.getInstance().getConstraintManager();

            AnnotatedTypeMirror lhsATM = atypeFactory.getAnnotatedType(node.getLeftOperand());
            AnnotatedTypeMirror rhsATM = atypeFactory.getAnnotatedType(node.getRightOperand());
            // Note: lhs and rhs either contains constant slots or var slots, resolved
            VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
            VariableSlot rhs = slotManager.getVariableSlot(rhsATM);

            Kind kind = node.getKind();
            switch (node.getKind()) {
                case PLUS:
                case MINUS:
                case MULTIPLY:
                case DIVIDE:
                case REMAINDER:
                    ArithmeticOperationKind opKind = ArithmeticOperationKind.fromTreeKind(kind);

                    VariableSlot res =
                            slotManager.getVariableSlot(atypeFactory.getAnnotatedType(node));
                    assert res instanceof ArithmeticVariableSlot;

                    ArithmeticVariableSlot avsRes = (ArithmeticVariableSlot) res;

                    // System.out.println(
                    // "\n=== units visitor " + avsRes + " = " + lhs + " " + opKind + " " + rhs);
                    // System.out.println(" " + lhs.getClass() + " " + rhs.getClass());
                    // System.out.println(
                    // " slot vals: " + avsRes.leftOperand + " " + avsRes.rightOperand);
                    // System.out.println(" " + avsRes.leftOperand.getClass() + " " +
                    // avsRes.leftOperand.getClass());
                    constraintManager.addArithmeticConstraint(opKind, lhs, rhs, avsRes);
                    break;
                default:
                    // TODO: replace with LUBSlot pending mier's PR
                    VariableSlot lubSlot =
                            slotManager.getVariableSlot(atypeFactory.getAnnotatedType(node));
                    // Create LUB constraint by default
                    constraintManager.addSubtypeConstraint(lhs, lubSlot);
                    constraintManager.addSubtypeConstraint(rhs, lubSlot);
                    break;
            }

        } else { // if (atypeFactory instanceof UnitsAnnotatedTypeFactory)
            UnitsAnnotatedTypeFactory atf = (UnitsAnnotatedTypeFactory) atypeFactory;

            AnnotationMirror lhsAM =
                    atf.getAnnotatedType(node.getLeftOperand()).getEffectiveAnnotationInHierarchy(
                            UnitsRepresentationUtils.getInstance().RAWUNITSINTERNAL);
            AnnotationMirror rhsAM =
                    atf.getAnnotatedType(node.getRightOperand()).getEffectiveAnnotationInHierarchy(
                            UnitsRepresentationUtils.getInstance().RAWUNITSINTERNAL);

            switch (node.getKind()) {
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

    // Slots created in ATF

    // Constraints created in Visitor

    // see
    // https://github.com/topnessman/immutability/blob/master/src/main/java/pico/inference/PICOInferenceVisitor.java
}
