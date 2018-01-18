package units;

import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.source.Result;
import org.checkerframework.javacutil.AnnotationUtils;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceVisitor;

public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {

    public UnitsVisitor(UnitsChecker checker, InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory, boolean infer) {
        super(checker, ichecker, factory, infer);
    }

    @Override
    public Void visitBinary(BinaryTree node, Void p) {
        if (!infer && atypeFactory instanceof UnitsAnnotatedTypeFactory) {
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
