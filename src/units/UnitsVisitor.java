package units;

import checkers.inference.InferenceChecker;
import checkers.inference.InferenceMain;
import checkers.inference.InferenceVisitor;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.VariableSlot;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.UnaryTree;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;
import units.representation.UnitsRepresentationUtils;
import units.util.UnitsTypecheckUtils;

public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {

    public UnitsVisitor(
            UnitsChecker checker,
            InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory,
            boolean infer) {
        super(checker, ichecker, factory, infer);
    }

    // @Override
    // public Void visitVariable(VariableTree node, Void p) {
    // super.visitVariable(node, p);
    //
    // if (infer) {
    // // For boxed primitive classes, we stub the constructors to be PolyUnit, thus there will
    // // be a VarAnnot created for each instance of PolyUnit.
    //
    // // An additional subtype constraint is generated here to ensure the VarAnnot is a
    // // subtype of the variable's VarAnnot.
    // UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();
    //
    // AnnotatedTypeMirror varATM = atypeFactory.getAnnotatedType(node);
    //
    // ExpressionTree expr = node.getInitializer();
    // if (expr != null) {
    // AnnotatedTypeMirror expATM = atypeFactory.getAnnotatedType(expr);
    //
    // System.out.println(" === var: " + node);
    // System.out.println(" == node initializer kind " + expr.getKind());
    //
    // AnnotationMirror varAM = varATM.getAnnotationInHierarchy(unitsRepUtils.VARANNOT);
    // AnnotationMirror expAM = expATM.getAnnotationInHierarchy(unitsRepUtils.VARANNOT);
    //
    // System.out.println(" === varATM " + varATM);
    // System.out.println(" === varAM " + varAM);
    //
    // System.out.println(" === expATM " + expATM);
    // System.out.println(" === expAM " + expAM);
    //
    // System.out.println("");
    // }
    //
    // }
    //
    // return null;
    // }

    // @Override
    // public Void visitAssignment(AssignmentTree node, Void p) {
    // if (infer) {
    // AnnotatedTypeMirror varATM = atypeFactory.getAnnotatedType(node.getVariable());
    // AnnotatedTypeMirror expATM = atypeFactory.getAnnotatedType(node.getExpression());
    // UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();
    //
    // AnnotationMirror varAM = varATM.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);
    // AnnotationMirror expAM = expATM.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);
    //
    // System.out.println(" === assign: " + node);
    //
    // System.out.println(" === varATM " + varATM);
    // System.out.println(" === varAM " + varAM);
    //
    // System.out.println(" === expATM " + expATM);
    // System.out.println(" === expAM " + expAM);
    //
    // System.out.println("");
    // }
    //
    // return super.visitAssignment(node, p);
    // }

    @Override
    public Void visitUnary(UnaryTree node, Void p) {
        // Note i++ in a for loop generates a subtype constraint that the type variable for i is a
        // supertype of raw units internal, this subtype doesn't need to be generated
        if ((node.getKind() == Kind.PREFIX_DECREMENT)
                || (node.getKind() == Kind.PREFIX_INCREMENT)
                || (node.getKind() == Kind.POSTFIX_DECREMENT)
                || (node.getKind() == Kind.POSTFIX_INCREMENT)) {
            return null;
        } else {
            return super.visitUnary(node, p);
        }
    }

    @Override
    public Void visitBinary(BinaryTree binaryTree, Void p) {
        // infer mode, adds constraints for binary operations
        if (infer) {
            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
            ConstraintManager constraintManager =
                    InferenceMain.getInstance().getConstraintManager();

            AnnotatedTypeMirror lhsATM = atypeFactory.getAnnotatedType(binaryTree.getLeftOperand());
            AnnotatedTypeMirror rhsATM =
                    atypeFactory.getAnnotatedType(binaryTree.getRightOperand());
            // Note: lhs and rhs either contains constant slots or var slots, resolved
            VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
            VariableSlot rhs = slotManager.getVariableSlot(rhsATM);

            Kind kind = binaryTree.getKind();
            switch (binaryTree.getKind()) {
                case PLUS:
                    // if either are string arguments, result is already a constant slot of
                    // dimensionless
                    if (TreeUtils.isStringConcatenation(binaryTree)) {
                        break;
                    } // else create arithmetic constraint
                case MINUS:
                case MULTIPLY:
                case DIVIDE:
                case REMAINDER:
                    ArithmeticOperationKind opKind = ArithmeticOperationKind.fromTreeKind(kind);
                    ArithmeticVariableSlot avsRes =
                            slotManager.getArithmeticVariableSlot(
                                    VariableAnnotator.treeToLocation(atypeFactory, binaryTree));
                    constraintManager.addArithmeticConstraint(opKind, lhs, rhs, avsRes);
                    break;
                case EQUAL_TO: // ==
                case NOT_EQUAL_TO: // !=
                case GREATER_THAN: // >
                case GREATER_THAN_EQUAL: // >=
                case LESS_THAN: // <
                case LESS_THAN_EQUAL: // <=
                    // result is already dimensionless for bools
                    constraintManager.addComparableConstraint(lhs, rhs);
                    break;
                default:
                    // TODO: replace with LUBSlot pending mier's PR
                    VariableSlot lubSlot =
                            slotManager.getVariableSlot(atypeFactory.getAnnotatedType(binaryTree));
                    // Create LUB constraint by default
                    constraintManager.addSubtypeConstraint(lhs, lubSlot);
                    constraintManager.addSubtypeConstraint(rhs, lubSlot);
                    break;
            }

            return super.visitBinary(binaryTree, p);
        }
        // typecheck mode

        // Note to self: in typecheck mode, always use getEffectiveAnnotationInHierarchy

        // if (atypeFactory instanceof UnitsAnnotatedTypeFactory)
        UnitsAnnotatedTypeFactory atf = (UnitsAnnotatedTypeFactory) atypeFactory;
        UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();

        AnnotatedTypeMirror lhsATM = atf.getAnnotatedType(binaryTree.getLeftOperand());
        AnnotatedTypeMirror rhsATM = atf.getAnnotatedType(binaryTree.getRightOperand());
        AnnotationMirror lhsAM = lhsATM.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);
        AnnotationMirror rhsAM = rhsATM.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);

        switch (binaryTree.getKind()) {
            case PLUS:
                // if it is not a string concatenation and the units don't match, issue warning
                // if (!TreeUtils.isStringConcatenation(binaryTree)
                // && !AnnotationUtils.areSame(lhsAM, rhsAM)) {
                // checker.report(Result.failure("addition.unit.mismatch",
                // atypeFactory.getAnnotationFormatter().formatAnnotationMirror(lhsAM),
                // atypeFactory.getAnnotationFormatter().formatAnnotationMirror(rhsAM)),
                // binaryTree);
                // }
                break;
            case MINUS:
                // if (!AnnotationUtils.areSame(lhsAM, rhsAM)) {
                // checker.report(Result.failure("subtraction.unit.mismatch",
                // atypeFactory.getAnnotationFormatter().formatAnnotationMirror(lhsAM),
                // atypeFactory.getAnnotationFormatter().formatAnnotationMirror(rhsAM)),
                // binaryTree);
                // }
                break;
            case EQUAL_TO: // ==
            case NOT_EQUAL_TO: // !=
            case GREATER_THAN: // >
            case GREATER_THAN_EQUAL: // >=
            case LESS_THAN: // <
            case LESS_THAN_EQUAL: // <=
                // comparable constraint: lhs <: rhs, or rhs <: lhs
                if (!(atypeFactory.getQualifierHierarchy().isSubtype(lhsAM, rhsAM)
                        || atypeFactory.getQualifierHierarchy().isSubtype(rhsAM, lhsAM))) {
                    checker.report(
                            Result.failure(
                                    "comparison.unit.mismatch",
                                    atypeFactory
                                            .getAnnotationFormatter()
                                            .formatAnnotationMirror(lhsAM),
                                    atypeFactory
                                            .getAnnotationFormatter()
                                            .formatAnnotationMirror(rhsAM)),
                            binaryTree);
                }
                // if (!AnnotationUtils.areSame(lhsAM, rhsAM)) {
                // }
            default:
                break;
        }

        return super.visitBinary(binaryTree, p);
    }

    // permit casts from dimensionless to a unit
    // cast to top are redundant but permitted
    // cast to bottom is usually nonsense, but can appear in inference results... so permitted
    @Override
    public Void visitTypeCast(TypeCastTree node, Void p) {
        // TODO: infer mode
        if (infer) {
            return super.visitTypeCast(node, p);
        }
        // typecheck mode

        // validate "node" instead of "node.getType()" to prevent duplicate errors.
        boolean valid = validateTypeOf(node) && validateTypeOf(node.getExpression());
        if (valid) {
            UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();

            // AnnotationMirror castType =
            // atypeFactory.getAnnotatedType(node).getAnnotationInHierarchy(unitsRepUtils.TOP);
            AnnotationMirror exprType =
                    atypeFactory
                            .getAnnotatedType(node.getExpression())
                            .getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);

            if (UnitsTypecheckUtils.unitsEqual(exprType, unitsRepUtils.DIMENSIONLESS)) {
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

    // We implicitly set DIMENSIONLESS as the type of all throwable and exceptions
    // We update the lower bounds here
    @Override
    protected Set<? extends AnnotationMirror> getExceptionParameterLowerBoundAnnotations() {
        Set<AnnotationMirror> lowerBounds = AnnotationUtils.createAnnotationSet();
        if (infer) {
            // In inference mode, the lower bound is the constant slot for @Dimensionless
            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
            ConstantSlot cs =
                    slotManager.createConstantSlot(
                            UnitsRepresentationUtils.getInstance().DIMENSIONLESS);
            lowerBounds.add(slotManager.getAnnotation(cs));
        } else {
            // In type check mode, the lower bound is @Dimensionless
            lowerBounds.add(UnitsRepresentationUtils.getInstance().DIMENSIONLESS);
        }
        return lowerBounds;
    }

    //    // Debug use, finds out number of calls to each instrumented method
    //    @Override
    //    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
    //        String methodName = TreeUtils.methodName(node).toString().intern();
    //
    //        ExecutableElement element = TreeUtils.elementFromUse(node);
    //        String classOfMethod = element.getEnclosingElement().toString().intern();
    //
    //        if (classOfMethod.contentEquals("java.lang.Math")) {
    //            switch (methodName) {
    //                case "cos":
    //                case "sin":
    //                case "tan":
    //                case "asin":
    //                case "acos":
    //                case "atan":
    //                case "atan2":
    //                case "sinh":
    //                case "cosh":
    //                case "tanh":
    //                case "toDegrees":
    //                case "toRadians":
    //                    System.out.println(" visited: " + classOfMethod + "." + methodName);
    //                    break;
    //                default:
    //                    break;
    //            }
    //        } else if (classOfMethod.contentEquals("java.lang.System")) {
    //            switch (methodName) {
    //                case "currentTimeMillis":
    //                case "nanoTime":
    //                    System.out.println(" visited: " + classOfMethod + "." + methodName);
    //                    break;
    //                default:
    //                    break;
    //            }
    //        } else if (classOfMethod.contentEquals("java.lang.Thread")) {
    //            switch (methodName) {
    //                case "sleep":
    //                    System.out.println(" visited: " + classOfMethod + "." + methodName);
    //                    break;
    //                default:
    //                    break;
    //            }
    //        }
    //
    //        return super.visitMethodInvocation(node, p);
    //    }

    // Slots created in ATF

    // Constraints created in Visitor

    // see
    // https://github.com/topnessman/immutability/blob/master/src/main/java/pico/inference/PICOInferenceVisitor.java
}
