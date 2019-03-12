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
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.CompoundAssignmentTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.UnaryTree;
import com.sun.source.util.TreePath;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.Modifier;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeFactory.ParameterizedExecutableType;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.BugInCF;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;
import org.checkerframework.javacutil.UserError;
import units.qual.Dimensionless;
import units.qual.UnitsAddition;
import units.qual.UnitsCompare;
import units.qual.UnitsDivision;
import units.qual.UnitsMultiplication;
import units.qual.UnitsSame;
import units.qual.UnitsSames;
import units.qual.UnitsSubtraction;
import units.qual.UnknownUnits;
import units.utils.UnitsRepresentationUtils;
import units.utils.UnitsTypecheckUtils;

/**
 * Units visitor.
 *
 * <p>Ensure consistent use of compound assignments.
 */
public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {
    /** reference to the units representation utilities library */
    protected final UnitsRepresentationUtils unitsRepUtils;

    /** reference to the units type check utilities library */
    protected final UnitsTypecheckUtils unitsTypecheckUtils;

    protected UnitsAnnotatedTypeFactory unitsATF;

    protected UnitsInferenceAnnotatedTypeFactory unitsIATF;
    protected SlotManager slotManager;
    protected ConstraintManager constraintManager;

    public UnitsVisitor(
            UnitsChecker checker,
            InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory,
            boolean infer) {
        super(checker, ichecker, factory, infer);

        if (!(factory instanceof UnitsAnnotatedTypeFactory
                || factory instanceof UnitsInferenceAnnotatedTypeFactory)) {
            throw new BugInCF(
                    "Incorrect class of type factory created "
                            + factory.getClass().getCanonicalName());
        }

        if (factory instanceof UnitsAnnotatedTypeFactory) {
            unitsATF = (UnitsAnnotatedTypeFactory) factory;
            unitsRepUtils = unitsATF.getUnitsRepresentationUtils();
            unitsTypecheckUtils = unitsATF.getUnitsTypecheckUtils();
        } else {
            unitsIATF = (UnitsInferenceAnnotatedTypeFactory) factory;
            unitsRepUtils = unitsIATF.getUnitsRepresentationUtils();
            unitsTypecheckUtils = unitsIATF.getUnitsTypecheckUtils();
            slotManager = InferenceMain.getInstance().getSlotManager();
            constraintManager = InferenceMain.getInstance().getConstraintManager();
        }
    }

    // TODO: work in progress to enable checking "type.invalid.annotations.on.use" errors
    //    /**
    //     * copy of super but with validateType enabled, so that it eventually calls {@link
    //     * #isValidUse(AnnotatedDeclaredType, AnnotatedDeclaredType, Tree)} below
    //     *
    //     * <p>TODO: two copies of "type.invalid.annotations.on.use" are issued, once due to {@link
    //     * #commonAssignmentCheck(AnnotatedTypeMirror, ExpressionTree, String)} during {@link
    //     * #visitVariable(com.sun.source.tree.VariableTree, Void)}, and once due to {@link
    //     * #visitNewClass(NewClassTree, Void)}, both calling {@link #validateTypeOf(Tree)}.
    // Deduplicate
    //     * if possible.
    //     */
    //    @Override
    //    public boolean validateTypeOf(Tree tree) {
    //        AnnotatedTypeMirror type;
    //        // It's quite annoying that there is no TypeTree.
    //        switch (tree.getKind()) {
    //            case PRIMITIVE_TYPE:
    //            case PARAMETERIZED_TYPE:
    //            case TYPE_PARAMETER:
    //            case ARRAY_TYPE:
    //            case UNBOUNDED_WILDCARD:
    //            case EXTENDS_WILDCARD:
    //            case SUPER_WILDCARD:
    //            case ANNOTATED_TYPE:
    //                type = atypeFactory.getAnnotatedTypeFromTypeTree(tree);
    //                break;
    //            case METHOD:
    //                type = atypeFactory.getMethodReturnType((MethodTree) tree);
    //                if (type == null || type.getKind() == TypeKind.VOID) {
    //                    // Nothing to do for void methods.
    //                    // Note that for a constructor the AnnotatedExecutableType does
    //                    // not use void as return type.
    //                    return true;
    //                }
    //                break;
    //            default:
    //                type = atypeFactory.getAnnotatedType(tree);
    //        }
    //        return validateType(tree, type);
    //    }

    /** override to allow uses of classes declared as {@link Dimensionless} with units */
    @Override
    public boolean isValidUse(
            AnnotatedDeclaredType declarationType, AnnotatedDeclaredType useType, Tree tree) {
        AnnotatedDeclaredType erasedDeclaredType = declarationType.getErased();
        AnnotationMirror anno =
                erasedDeclaredType.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);
        return AnnotationUtils.areSame(anno, unitsRepUtils.DIMENSIONLESS)
                || super.isValidUse(declarationType, useType, tree);
    }

    @Override
    public Void visitUnary(UnaryTree node, Void p) {
        /** Unary increment and decrement is always type safe */
        if ((node.getKind() == Kind.PREFIX_DECREMENT)
                || (node.getKind() == Kind.PREFIX_INCREMENT)
                || (node.getKind() == Kind.POSTFIX_DECREMENT)
                || (node.getKind() == Kind.POSTFIX_INCREMENT)) {
            return null;
        } else {
            return super.visitUnary(node, p);
        }
    }

    @SuppressWarnings("fallthrough")
    @Override
    public Void visitBinary(BinaryTree binaryTree, Void p) {
        // infer mode, adds constraints for binary operations
        if (infer) {
            // AnnotatedTypeMirror lhsATM =
            // atypeFactory.getAnnotatedType(binaryTree.getLeftOperand());
            // AnnotatedTypeMirror rhsATM =
            // atypeFactory.getAnnotatedType(binaryTree.getRightOperand());
            // // Note: lhs and rhs either contains constant slots or var slots, resolved
            // VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
            // VariableSlot rhs = slotManager.getVariableSlot(rhsATM);

            // Candidate Fix 1:
            AnnotatedTypeMirror lhsATM = unitsIATF.getAnnotatedType(binaryTree.getLeftOperand());
            AnnotatedTypeMirror rhsATM = unitsIATF.getAnnotatedType(binaryTree.getRightOperand());
            // For types such as T extends @VarAnnot() Class, use @VarAnnot(), by grabbing
            // the effective annotation in varannot hierarchy
            AnnotationMirror lhsEAM =
                    lhsATM.getEffectiveAnnotationInHierarchy(unitsIATF.getVarAnnot());
            AnnotationMirror rhsEAM =
                    rhsATM.getEffectiveAnnotationInHierarchy(unitsIATF.getVarAnnot());
            Slot lhs = slotManager.getSlot(lhsEAM);
            Slot rhs = slotManager.getSlot(rhsEAM);

            // System.err.println("");
            //
            // System.err.println("lhsATM: " + lhsATM);
            // System.err.println("lhs EAs: " + lhsATM.getEffectiveAnnotations());
            // System.err.println("lhs: " + lhs);
            // System.err.println("lhsEAM: " + lhsEAM);
            // System.err.println("lhsES: " + lhsES);
            // System.err.println("");
            //
            // System.err.println("rhsATM: " + rhsATM);
            // System.err.println("rhs EAs: " + rhsATM.getEffectiveAnnotations());
            // System.err.println("rhs: " + rhs);
            // System.err.println("rhsEAM: " + rhsEAM);
            // System.err.println("rhsES: " + rhsES);
            // System.err.println("");
            //
            // System.err.println("");

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
        AnnotatedTypeMirror lhsATM = unitsATF.getAnnotatedType(binaryTree.getLeftOperand());
        AnnotatedTypeMirror rhsATM = unitsATF.getAnnotatedType(binaryTree.getRightOperand());
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
                checkCompare(binaryTree, lhsAM, rhsAM);
            default:
                break;
        }

        return super.visitBinary(binaryTree, p);
    }

    // TODO: check this rule
    @Override
    public Void visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
            return null;
        }

        // typecheck mode
        ExpressionTree var = node.getVariable();
        ExpressionTree expr = node.getExpression();
        AnnotatedTypeMirror varType = atypeFactory.getAnnotatedType(var);
        AnnotatedTypeMirror exprType = atypeFactory.getAnnotatedType(expr);

        Kind kind = node.getKind();

        if ((kind == Kind.PLUS_ASSIGNMENT || kind == Kind.MINUS_ASSIGNMENT)) {
            if (!atypeFactory.getTypeHierarchy().isSubtype(exprType, varType)) {
                checker.report(
                        Result.failure("compound.assignment.type.incompatible", varType, exprType),
                        node);
            }
        } else if (AnnotationUtils.areSame(
                exprType.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP), unitsRepUtils.TOP)) {
            // Only allow mul/div with unqualified units
            checker.report(
                    Result.failure("compound.assignment.type.incompatible", varType, exprType),
                    node);
        }

        return null; // super.visitCompoundAssignment(node, p);
    }

    // permit casts from DIMENSIONLESS to any unit. In inference mode this is required for
    // post-inference type check stage as units for number literals are inserted as a "cast".
    @Override
    public Void visitTypeCast(TypeCastTree node, Void p) {
        if (infer) {
            // TODO: infer mode
            // in infer mode, we are generating constraints for explicitly written casts in
            // code we do not generate constraints here for the casts inserted for literals
            // from inference output
            return super.visitTypeCast(node, p);
        }

        // typecheck mode
        // validate "node" instead of "node.getType()" to prevent duplicate errors.
        boolean valid = validateTypeOf(node) && validateTypeOf(node.getExpression());
        if (valid) {
            // AnnotationMirror castType =
            // atypeFactory.getAnnotatedType(node).getAnnotationInHierarchy(unitsRepUtils.TOP);
            AnnotationMirror exprType =
                    atypeFactory
                            .getAnnotatedType(node.getExpression())
                            .getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);

            // If expression type is dimensionless, permit it to be casted to anything
            if (unitsTypecheckUtils.unitsEqual(exprType, unitsRepUtils.DIMENSIONLESS)) {
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
            ConstantSlot cs = slotManager.createConstantSlot(unitsRepUtils.DIMENSIONLESS);
            lowerBounds.add(slotManager.getAnnotation(cs));
        } else {
            // In type check mode, the lower bound is @Dimensionless
            lowerBounds.add(unitsRepUtils.DIMENSIONLESS);
        }
        return lowerBounds;
    }

    @Override
    public Void visitNewClass(NewClassTree node, Void p) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
            return null;
        }

        // typecheck mode
        super.visitNewClass(node, p);

        ParameterizedExecutableType mType = atypeFactory.constructorFromUse(node);
        AnnotatedExecutableType invokedMethod = mType.executableType;
        ExecutableElement methodElement = invokedMethod.getElement();
        // List<AnnotatedTypeMirror> typeargs = mType.typeArgs;

        // System.err.println(" methodElement " + methodElement);

        // Build up a list of ATMs corresponding to the index convention used in the Units
        // method meta-annotations. null values are inserted if there is no possible ATM for
        // that index position.
        List<AnnotatedTypeMirror> atms = new ArrayList<>();
        atms.add(atypeFactory.getAnnotatedType(node));

        ExpressionTree receiver = TreeUtils.getReceiverTree(node);
        // System.err.println(" receiver " + receiver);

        // ATM for argument to the formal "this" parameter
        if (receiver != null) {
            AnnotatedTypeMirror receiverATM = atypeFactory.getAnnotatedType(receiver);
            atms.add(receiverATM);
        } else {
            atms.add(null);
        }

        for (ExpressionTree arg : node.getArguments()) {
            AnnotatedTypeMirror argATM = atypeFactory.getAnnotatedType(arg);
            // System.err.println(" arg " + arg + " type " + argATM);
            atms.add(argATM);
        }

        // multiple meta-annotations are allowed on each method
        for (AnnotationMirror anno : atypeFactory.getDeclAnnotations(methodElement)) {
            if (AnnotationUtils.areSameByClass(anno, UnitsAddition.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsSubtraction.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsMultiplication.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsDivision.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsSames.class)) {
                for (AnnotationMirror same :
                        AnnotationUtils.getElementValueArray(
                                anno, "value", AnnotationMirror.class, false)) {
                    checkMethodUnitsSame(node, invokedMethod, same, atms);
                }
            } else if (AnnotationUtils.areSameByClass(anno, UnitsSame.class)) {
                checkMethodUnitsSame(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsCompare.class)) {
                checkMethodUnitsCompare(node, invokedMethod, anno, atms);
            }
        }

        return null;
    }

    /**
     * Override to not issue "cast.unsafe.constructor.invocation" warnings for classes declared as
     * {@link UnknownUnits} as it is a common use case in Units checker. However, issue
     * "cast.unsafe.constructor.invocation" if the computed polymorphic return type of a polymorphic
     * constructor is being cast to an incomparable unit.
     */
    @Override
    protected boolean checkConstructorInvocation(
            AnnotatedDeclaredType invocation,
            AnnotatedExecutableType constructor,
            NewClassTree newClassTree) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        // copied from super implementation
        AnnotatedDeclaredType computedReturnType =
                (AnnotatedDeclaredType) constructor.getReturnType();
        // When an interface is used as the identifier in an anonymous class (e.g. new Comparable()
        // {}) the constructor method will be Object.init() {} which has an Object return type When
        // TypeHierarchy attempts to convert it to the supertype (e.g. Comparable) it will return
        // null from asSuper and return false for the check. Instead, copy the primary annotations
        // to the declared type and then do a subtyping check.
        if (invocation.getUnderlyingType().asElement().getKind().isInterface()
                && TypesUtils.isObject(computedReturnType.getUnderlyingType())) {
            final AnnotatedDeclaredType retAsDt = invocation.deepCopy();
            retAsDt.replaceAnnotations(computedReturnType.getAnnotations());
            computedReturnType = retAsDt;
        }

        // issue "cast.unsafe.constructor.invocation" if the computed polymorphic return type of a
        // polymorphic constructor is being cast to an incomparable unit
        AnnotatedDeclaredType declaredReturnType =
                (AnnotatedDeclaredType)
                        atypeFactory.getAnnotatedType(constructor.getElement()).getReturnType();
        AnnotationMirror declaredReturnAnno =
                declaredReturnType.getAnnotationInHierarchy(unitsRepUtils.TOP);
        if (unitsRepUtils.isPolymorphic(declaredReturnAnno)
                && !atypeFactory.getTypeHierarchy().isSubtype(computedReturnType, invocation)) {
            checker.report(
                    Result.warning(
                            "cast.unsafe.constructor.invocation",
                            computedReturnType.toString(true),
                            invocation.toString(true)),
                    newClassTree);
            return false;
        }

        // do not issue warnings if the computed return type is top
        if (AnnotationUtils.areSame(
                computedReturnType.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP),
                unitsRepUtils.TOP)) {
            return true;
        }

        return super.checkConstructorInvocation(invocation, constructor, newClassTree);
    }

    // Because units permits subclasses to return objects with units, giving a
    // "super.invocation.invalid" warning at every declaration of a subclass constructor is annoying
    // to user of units, we override the check here to always permit the invocation of a super
    // constructor returning dimensionless values
    @Override
    protected void checkSuperConstructorCall(MethodInvocationTree node) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        if (!TreeUtils.isSuperCall(node)) {
            return;
        }
        TreePath path = atypeFactory.getPath(node);
        MethodTree enclosingMethod = TreeUtils.enclosingMethod(path);
        if (TreeUtils.isConstructor(enclosingMethod)) {
            AnnotatedTypeMirror superType = atypeFactory.getAnnotatedType(node);
            AnnotationMirror superTypeMirror =
                    superType.getAnnotationInHierarchy(unitsRepUtils.TOP);
            if (!AnnotationUtils.areSame(superTypeMirror, unitsRepUtils.DIMENSIONLESS)) {
                super.checkSuperConstructorCall(node);
            }
        }
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        super.visitMethodInvocation(node, p);

        ParameterizedExecutableType mType = atypeFactory.methodFromUse(node);
        AnnotatedExecutableType invokedMethod = mType.executableType;
        ExecutableElement methodElement = invokedMethod.getElement();
        // List<AnnotatedTypeMirror> typeargs = mType.typeArgs;

        // System.err.println(" invokedMethod " + invokedMethod.getErased());
        // System.err.println(" methodElement " + methodElement);

        // Build up a list of ATMs corresponding to the index convention used in the Units
        // method meta-annotations. null values are inserted if there is no possible ATM for
        // that index position.
        List<AnnotatedTypeMirror> atms = new ArrayList<>();
        atms.add(atypeFactory.getAnnotatedType(node));

        boolean isStaticMethod = methodElement.getModifiers().contains(Modifier.STATIC);
        // System.err.println(" isStaticMethod " + isStaticMethod);

        ExpressionTree receiver = TreeUtils.getReceiverTree(node);
        // System.err.println(" receiver " + receiver);

        // ATM for argument to the formal "this" parameter
        if (receiver != null && !isStaticMethod) {
            AnnotatedTypeMirror receiverATM = atypeFactory.getAnnotatedType(receiver);
            atms.add(receiverATM);
        } else {
            atms.add(null);
        }

        for (ExpressionTree arg : node.getArguments()) {
            AnnotatedTypeMirror argATM = atypeFactory.getAnnotatedType(arg);
            // System.err.println(" arg " + arg + " type " + argATM);
            atms.add(argATM);
        }

        // multiple meta-annotations are allowed on each method
        for (AnnotationMirror anno : atypeFactory.getDeclAnnotations(methodElement)) {
            if (AnnotationUtils.areSameByClass(anno, UnitsAddition.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsSubtraction.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsMultiplication.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsDivision.class)) {
                checkMethodUnitsArithmetic(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsSames.class)) {
                for (AnnotationMirror same :
                        AnnotationUtils.getElementValueArray(
                                anno, "value", AnnotationMirror.class, false)) {
                    checkMethodUnitsSame(node, invokedMethod, same, atms);
                }
            } else if (AnnotationUtils.areSameByClass(anno, UnitsSame.class)) {
                checkMethodUnitsSame(node, invokedMethod, anno, atms);
            } else if (AnnotationUtils.areSameByClass(anno, UnitsCompare.class)) {
                checkMethodUnitsCompare(node, invokedMethod, anno, atms);
            }
        }

        //    // Debug use, finds out number of calls to each instrumented method
        //    String methodName = TreeUtils.methodName(node).toString().intern();
        //
        //    ExecutableElement element = TreeUtils.elementFromUse(node);
        //    String classOfMethod = element.getEnclosingElement().toString().intern();
        //
        //    if (classOfMethod.contentEquals("java.lang.Math")) {
        //        switch (methodName) {
        //            case "cos":
        //            case "sin":
        //            case "tan":
        //            case "asin":
        //            case "acos":
        //            case "atan":
        //            case "atan2":
        //            case "sinh":
        //            case "cosh":
        //            case "tanh":
        //            case "toDegrees":
        //            case "toRadians":
        //                System.err.println(" visited: " + classOfMethod + "." + methodName);
        //                break;
        //            default:
        //                break;
        //        }
        //    } else if (classOfMethod.contentEquals("java.lang.System")) {
        //        switch (methodName) {
        //            case "currentTimeMillis":
        //            case "nanoTime":
        //                System.err.println(" visited: " + classOfMethod + "." + methodName);
        //                break;
        //            default:
        //                break;
        //        }
        //    } else if (classOfMethod.contentEquals("java.lang.Thread")) {
        //        switch (methodName) {
        //            case "sleep":
        //                System.err.println(" visited: " + classOfMethod + "." + methodName);
        //                break;
        //            default:
        //                break;
        //        }
        //    }
        return null;
    }

    protected void checkMethodUnitsArithmetic(
            Tree node,
            AnnotatedExecutableType invokedMethod,
            AnnotationMirror anno,
            List<AnnotatedTypeMirror> atms) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        int leftOperandPos = unitsTypecheckUtils.getIntElementValue(anno, "larg");
        int rightOperandPos = unitsTypecheckUtils.getIntElementValue(anno, "rarg");
        int resultPos = unitsTypecheckUtils.getIntElementValue(anno, "res");

        // The check is done here instead of visitMethod() in case an improper meta-annotation was
        // declared in a stub
        validatePositionIndex(invokedMethod, anno, leftOperandPos);
        validatePositionIndex(invokedMethod, anno, rightOperandPos);
        validatePositionIndex(invokedMethod, anno, resultPos);

        if (resultPos == leftOperandPos) {
            throw new UserError(
                    "The indices res and larg cannot be the same for meta-annotation "
                            + anno
                            + " declared on method "
                            + invokedMethod);
        }

        if (resultPos == rightOperandPos) {
            throw new UserError(
                    "The indices res and rarg cannot be the same for meta-annotation "
                            + anno
                            + " declared on method "
                            + invokedMethod);
        }

        if (leftOperandPos == rightOperandPos) {
            throw new UserError(
                    "The indices larg and rarg cannot be the same for meta-annotation "
                            + anno
                            + " declared on method "
                            + invokedMethod);
        }
    }

    protected void checkMethodUnitsSame(
            Tree node,
            AnnotatedExecutableType invokedMethod,
            AnnotationMirror same,
            List<AnnotatedTypeMirror> atms) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        int fstPos = unitsTypecheckUtils.getIntElementValue(same, "fst");
        int sndPos = unitsTypecheckUtils.getIntElementValue(same, "snd");

        // The check is done here instead of visitMethod() in case an improper meta-annotation was
        // declared in a stub
        validatePositionIndex(invokedMethod, same, fstPos);
        validatePositionIndex(invokedMethod, same, sndPos);

        if (fstPos == sndPos) {
            throw new UserError(
                    "The indices fst and snd cannot be the same for meta-annotation "
                            + same
                            + " declared on method "
                            + invokedMethod);
        }

        AnnotatedTypeMirror fst = atms.get(fstPos + 1);
        AnnotatedTypeMirror snd = atms.get(sndPos + 1);

        AnnotationMirror fstAM = fst.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);
        AnnotationMirror sndAM = snd.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);

        if (fstPos != -1 && sndPos != -1 && !unitsTypecheckUtils.unitsEqual(fstAM, sndAM)) {
            checker.report(Result.failure("units.differ", fst, snd), node);
        }
    }

    protected void checkMethodUnitsCompare(
            Tree node,
            AnnotatedExecutableType invokedMethod,
            AnnotationMirror same,
            List<AnnotatedTypeMirror> atms) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        int fstPos = unitsTypecheckUtils.getIntElementValue(same, "fst");
        int sndPos = unitsTypecheckUtils.getIntElementValue(same, "snd");

        // TODO: for compare, -1 is not allowed
        // The check is done here instead of visitMethod() in case an improper meta-annotation was
        // declared in a stub
        validatePositionIndex(invokedMethod, same, fstPos);
        validatePositionIndex(invokedMethod, same, sndPos);

        if (fstPos == sndPos) {
            throw new UserError(
                    "The indices fst and snd cannot be the same for meta-annotation "
                            + same
                            + " declared on method "
                            + invokedMethod);
        }

        AnnotatedTypeMirror fst = atms.get(fstPos + 1);
        AnnotatedTypeMirror snd = atms.get(sndPos + 1);

        AnnotationMirror fstAM = fst.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);
        AnnotationMirror sndAM = snd.getEffectiveAnnotationInHierarchy(unitsRepUtils.TOP);

        checkCompare(node, fstAM, sndAM);
    }

    protected void checkCompare(Tree node, AnnotationMirror fstAM, AnnotationMirror sndAM) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        if (!unitsTypecheckUtils.unitsComparable(atypeFactory, fstAM, sndAM)) {
            checker.report(
                    Result.failure(
                            "comparison.unit.mismatch",
                            atypeFactory.getAnnotationFormatter().formatAnnotationMirror(fstAM),
                            atypeFactory.getAnnotationFormatter().formatAnnotationMirror(sndAM)),
                    node);
        }
    }

    // TODO: varargs
    protected void validatePositionIndex(
            AnnotatedExecutableType invokedMethod, AnnotationMirror same, int pos) {
        // infer mode, adds constraints
        if (infer) {
            // TODO
        }

        // typecheck mode
        boolean lowerBoundValid = -1 <= pos;
        boolean upperBoundValid = pos <= invokedMethod.getElement().getParameters().size();

        if (!lowerBoundValid || (!invokedMethod.isVarArgs() && !upperBoundValid)) {
            throw new UserError(
                    "The index "
                            + pos
                            + " is invalid for meta-annotation "
                            + same
                            + " declared on method "
                            + invokedMethod);
        }
    }
}
