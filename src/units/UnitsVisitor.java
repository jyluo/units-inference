package units;

import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.TypeCastTree;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceMain;
import checkers.inference.InferenceVisitor;
import checkers.inference.SlotManager;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.VariableSlot;
import units.representation.UnitsRepresentationUtils;
import units.util.UnitsTypecheckUtils;

public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {

    public UnitsVisitor(UnitsChecker checker, InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory, boolean infer) {
        super(checker, ichecker, factory, infer);
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
            UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();

            AnnotationMirror lhsAM = atf.getAnnotatedType(node.getLeftOperand())
                    .getEffectiveAnnotationInHierarchy(unitsRepUtils.RAWUNITSINTERNAL);
            AnnotationMirror rhsAM = atf.getAnnotatedType(node.getRightOperand())
                    .getEffectiveAnnotationInHierarchy(unitsRepUtils.RAWUNITSINTERNAL);

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

    // permit casts from dimensionless to a unit
    // cast to top are redundant but permitted
    // cast to bottom are forbidden
    @Override
    public Void visitTypeCast(TypeCastTree node, Void p) {
        // TODO: infer mode
        if (infer) {
            return super.visitTypeCast(node, p);
        }

        // validate "node" instead of "node.getType()" to prevent duplicate errors.
        boolean valid = validateTypeOf(node) && validateTypeOf(node.getExpression());
        if (valid) {
            UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();

            AnnotationMirror castType =
                    atypeFactory.getAnnotatedType(node).getAnnotationInHierarchy(unitsRepUtils.TOP);
            AnnotationMirror exprType = atypeFactory.getAnnotatedType(node.getExpression())
                    .getAnnotationInHierarchy(unitsRepUtils.TOP);

            if (UnitsTypecheckUtils.unitsEqual(exprType, unitsRepUtils.DIMENSIONLESS)
                    && !UnitsTypecheckUtils.unitsEqual(castType, unitsRepUtils.BOTTOM)) {
                if (atypeFactory.getDependentTypesHelper() != null) {
                    AnnotatedTypeMirror type = atypeFactory.getAnnotatedType(node);
                    atypeFactory.getDependentTypesHelper().checkType(type, node.getType());
                }

                // perform scan and reduce as per super.super.visitTypeCast()
                Void r = scan(node.getType(), p);
                r = reduce(scan(node.getExpression(), p), r);
                return r;
            }
        }
        return super.visitTypeCast(node, p);
    }

    // Slots created in ATF

    // Constraints created in Visitor

    // see
    // https://github.com/topnessman/immutability/blob/master/src/main/java/pico/inference/PICOInferenceVisitor.java
}
