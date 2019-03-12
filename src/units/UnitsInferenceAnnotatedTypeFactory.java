package units;

import checkers.inference.InferenceAnnotatedTypeFactory;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceQualifierHierarchy;
import checkers.inference.InferenceTreeAnnotator;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.AnnotationLocation;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import java.lang.annotation.Annotation;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.Name;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.qual.LiteralKind;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFormatter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.AnnotationClassLoader;
import org.checkerframework.framework.type.DefaultAnnotatedTypeFormatter;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.framework.util.AnnotationFormatter;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.Pair;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.UserError;
import units.utils.UnitsInferenceRepresentationUtils;
import units.utils.UnitsRepresentationUtils;
import units.utils.UnitsTypecheckUtils;

public class UnitsInferenceAnnotatedTypeFactory extends InferenceAnnotatedTypeFactory {
    protected final UnitsAnnotatedTypeFactory unitsATF;

    /**
     * reference to the {@link UnitsAnnotationFormatter} instance for formatting units in warnings
     */
    protected UnitsAnnotationFormatter unitsAnnotationFormatter;

    /** reference to the units representation utilities library */
    protected final UnitsInferenceRepresentationUtils unitsRepUtils;

    /** reference to the units type check utilities library */
    protected final UnitsTypecheckUtils unitsTypecheckUtils;

    public UnitsInferenceAnnotatedTypeFactory(
            InferenceChecker inferenceChecker,
            BaseAnnotatedTypeFactory realTypeFactory,
            InferrableChecker realChecker,
            SlotManager slotManager,
            ConstraintManager constraintManager) {
        super(
                inferenceChecker,
                false,
                realTypeFactory,
                realChecker,
                slotManager,
                constraintManager);
        unitsATF = (UnitsAnnotatedTypeFactory) realTypeFactory;

        // Should already be initialized in the real ATF
        unitsRepUtils = unitsATF.getUnitsRepresentationUtils();
        unitsTypecheckUtils = unitsATF.getUnitsTypecheckUtils();

        // and it should already have some base units
        if (unitsRepUtils.baseUnits().isEmpty()) {
            throw new UserError("Must supply at least 1 base unit to use Units Checker");
        }

        // unitsRepUtils.VARANNOT = getVarAnnot();

        // build in the same way as DefaultSlotManager's varannot
        // AnnotationBuilder builder = new AnnotationBuilder(processingEnv,
        // VarAnnot.class);
        // builder.setValue("value", -1);
        // unitsRepUtils.VARANNOT = builder.build();

        unitsAnnotationFormatter.postInit(unitsRepUtils);

        postInit();
    }

    public UnitsInferenceRepresentationUtils getUnitsRepresentationUtils() {
        return unitsRepUtils;
    }

    public UnitsTypecheckUtils getUnitsTypecheckUtils() {
        return unitsTypecheckUtils;
    }

    @Override
    protected AnnotationClassLoader createAnnotationClassLoader() {
        // Use the UnitsAnnotationClassLoader instead of the default one
        return new UnitsAnnotationClassLoader(checker);
    }

    // In Inference ATF, this returns the set of real qualifiers
    @Override
    protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
        // get all the loaded annotations
        Set<Class<? extends Annotation>> qualSet = new HashSet<Class<? extends Annotation>>();
        // Super grabs all supported qualifiers from the real qualifier hierarchy
        // and also puts in VarAnnot
        qualSet.addAll(super.createSupportedTypeQualifiers());

        // System.err.println( " --- quals = " + qualSet );

        // // load all the external units
        // loadAllExternalUnits();
        //
        // // copy all loaded external Units to qual set
        // qualSet.addAll(externalQualsMap.values());

        return qualSet;
    }

    // In Inference ATF, this returns the alias for a given real qualifier
    @Override
    public AnnotationMirror canonicalAnnotation(AnnotationMirror anno) {
        // TODO: cache results
        AnnotationMirror result = realTypeFactory.canonicalAnnotation(anno);
        // System.err.println(" === Aliasing: " + anno.toString() + " ==> " + result);

        if (result == null) {
            result = super.canonicalAnnotation(anno);
        }
        return result;
    }

    // for use in AnnotatedTypeMirror.toString()
    @Override
    protected AnnotatedTypeFormatter createAnnotatedTypeFormatter() {
        boolean printVerboseGenerics = checker.hasOption("printVerboseGenerics");
        return new DefaultAnnotatedTypeFormatter(
                createAnnotationFormatter(),
                printVerboseGenerics,
                // -AprintVerboseGenerics implies -AprintAllQualifiers
                printVerboseGenerics || checker.hasOption("printAllQualifiers"));
    }

    // for use in generating error outputs
    @Override
    protected AnnotationFormatter createAnnotationFormatter() {
        if (unitsAnnotationFormatter == null) {
            unitsAnnotationFormatter = new UnitsAnnotationFormatter();
        }
        return unitsAnnotationFormatter;
    }

    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new UnitsInferenceQualifierHierarchy(factory);
    }

    private final class UnitsInferenceQualifierHierarchy extends InferenceQualifierHierarchy {
        public UnitsInferenceQualifierHierarchy(MultiGraphFactory multiGraphFactory) {
            super(multiGraphFactory);
        }

        @Override
        protected Set<AnnotationMirror> findTops(
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypes) {
            Set<AnnotationMirror> tops = super.findTops(supertypes);
            tops.add(unitsRepUtils.TOP);
            tops.remove(unitsRepUtils.RAWUNITSREP);

            // remove RAWUNITSREP in supertypes
            assert supertypes.containsKey(unitsRepUtils.RAWUNITSREP);
            supertypes.remove(unitsRepUtils.RAWUNITSREP);
            // add TOP to supertypes
            supertypes.put(unitsRepUtils.TOP, Collections.emptySet());

            // System.err.println(" supertypes {");
            // for (Entry<?, ?> e : supertypes.entrySet()) {
            // System.err.println(" " + e.getKey() + " -> " + e.getValue());
            // }

            return tops;
        }

        @Override
        protected Set<AnnotationMirror> findBottoms(
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypes) {
            Set<AnnotationMirror> bottoms = super.findBottoms(supertypes);
            bottoms.add(unitsRepUtils.BOTTOM);
            bottoms.remove(unitsRepUtils.TOP);

            // set direct supertypes of BOTTOM and add to supertypes
            Set<AnnotationMirror> bottomSupers = new LinkedHashSet<>();
            bottomSupers.add(unitsRepUtils.POLYUNIT);
            bottomSupers.add(unitsRepUtils.POLYALL);
            bottomSupers.add(unitsRepUtils.TOP);
            supertypes.put(unitsRepUtils.BOTTOM, bottomSupers);

            // System.err.println(" supertypes {");
            // for (Entry<?, ?> e : supertypes.entrySet()) {
            // System.err.println(" " + e.getKey() + " -> " + e.getValue());
            // }

            return bottoms;
        }

        /**
         * Programmatically set {@link UnitsRepresentationUtils#POLYUNIT} and {@link
         * UnitsRepresentationUtils#POLYALL} as the polymorphic qualifiers
         */
        @Override
        protected void addPolyRelations(
                QualifierHierarchy qualHierarchy,
                Map<AnnotationMirror, Set<AnnotationMirror>> supertypes,
                Map<AnnotationMirror, AnnotationMirror> polyQualifiers,
                Set<AnnotationMirror> tops,
                Set<AnnotationMirror> bottoms) {

            // polyQualifiers {null=@PolyAll, @UnitsRep=@PolyUnit}
            // replace RAWUNITSREP -> @PolyUnit with TOP -> @PolyUnit
            // Build up a replacement map by looping through polyQualifiers as it is a simple hash
            // map. The null key causes crashes if not handled correctly.
            Map<AnnotationMirror, AnnotationMirror> updatedPolyQualifiers = new HashMap<>();
            for (Entry<AnnotationMirror, AnnotationMirror> e : polyQualifiers.entrySet()) {
                if (AnnotationUtils.areSame(e.getKey(), unitsRepUtils.RAWUNITSREP)) {
                    updatedPolyQualifiers.put(unitsRepUtils.TOP, e.getValue());
                } else {
                    updatedPolyQualifiers.put(e.getKey(), e.getValue());
                }
            }
            polyQualifiers.clear();
            polyQualifiers.putAll(updatedPolyQualifiers);

            // add @PolyAll -> TOP to supertypes
            Set<AnnotationMirror> polyAllSupers = AnnotationUtils.createAnnotationSet();
            polyAllSupers.add(unitsRepUtils.TOP);
            supertypes.put(unitsRepUtils.POLYALL, Collections.unmodifiableSet(polyAllSupers));

            // add @PolyUnit -> {@PolyAll, TOP} to supertypes
            Set<AnnotationMirror> polyUnitSupers = AnnotationUtils.createAnnotationSet();
            polyUnitSupers.add(unitsRepUtils.POLYALL);
            polyUnitSupers.add(unitsRepUtils.TOP);
            supertypes.put(unitsRepUtils.POLYUNIT, Collections.unmodifiableSet(polyUnitSupers));

            // System.err.println(" POST ");
            // System.err.println(" supertypes {");
            // for (Entry<?, ?> e : supertypes.entrySet()) {
            // System.err.println(" " + e.getKey() + " -> " + e.getValue());
            // }
            // System.err.println(" }");
            // System.err.println(" polyQualifiers " + polyQualifiers);
            // System.err.println(" tops " + tops);
            // System.err.println(" bottoms " + bottoms);
            // System.err.println();
        }
    }

    @Override
    public VariableAnnotator createVariableAnnotator() {
        return new UnitsVariableAnnotator(
                this, realTypeFactory, realChecker, slotManager, constraintManager);
    }

    private final class UnitsVariableAnnotator extends VariableAnnotator {

        public UnitsVariableAnnotator(
                InferenceAnnotatedTypeFactory typeFactory,
                AnnotatedTypeFactory realTypeFactory,
                InferrableChecker realChecker,
                SlotManager slotManager,
                ConstraintManager constraintManager) {
            super(typeFactory, realTypeFactory, realChecker, slotManager, constraintManager);
        }

        @Override
        public void handleBinaryTree(AnnotatedTypeMirror atm, BinaryTree binaryTree) {
            // Super creates an LUB constraint by default, we create an VariableSlot here
            // instead for the result of the binary op and create LUB constraint in units
            // visitor.
            if (treeToVarAnnoPair.containsKey(binaryTree)) {
                atm.replaceAnnotations(treeToVarAnnoPair.get(binaryTree).second);
            } else {
                // grab slots for the component (only for lub slot)
                AnnotatedTypeMirror lhsATM =
                        inferenceTypeFactory.getAnnotatedType(binaryTree.getLeftOperand());
                AnnotatedTypeMirror rhsATM =
                        inferenceTypeFactory.getAnnotatedType(binaryTree.getRightOperand());
                VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
                VariableSlot rhs = slotManager.getVariableSlot(rhsATM);

                // create varslot for the result of the binary tree computation
                // note: constraints for binary ops are added in UnitsVisitor
                VariableSlot result;
                switch (binaryTree.getKind()) {
                    case PLUS:
                        // if it is a string concatenation, result is dimensionless
                        if (TreeUtils.isStringConcatenation(binaryTree)) {
                            result = slotManager.createConstantSlot(unitsRepUtils.DIMENSIONLESS);
                            break;
                        } // else create arithmetic slot
                    case MINUS:
                    case MULTIPLY:
                    case DIVIDE:
                    case REMAINDER:
                        result =
                                slotManager.createArithmeticVariableSlot(
                                        VariableAnnotator.treeToLocation(
                                                inferenceTypeFactory, binaryTree));
                        break;
                    case CONDITIONAL_AND: // &&
                    case CONDITIONAL_OR: // ||
                    case LOGICAL_COMPLEMENT: // !
                    case EQUAL_TO: // ==
                    case NOT_EQUAL_TO: // !=
                    case GREATER_THAN: // >
                    case GREATER_THAN_EQUAL: // >=
                    case LESS_THAN: // <
                    case LESS_THAN_EQUAL: // <=
                        result = slotManager.createConstantSlot(unitsRepUtils.DIMENSIONLESS);
                        break;
                    default:
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                }

                // insert varAnnot of the slot into the ATM
                AnnotationMirror resultAM = slotManager.getAnnotation(result);
                atm.clearAnnotations();
                atm.replaceAnnotation(resultAM);

                // add to cache
                Set<AnnotationMirror> resultSet = AnnotationUtils.createAnnotationSet();
                resultSet.add(resultAM);
                final Pair<VariableSlot, Set<? extends AnnotationMirror>> varATMPair =
                        Pair.of(slotManager.getVariableSlot(atm), resultSet);
                treeToVarAnnoPair.put(binaryTree, varATMPair);
            }
        }
    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(
                new UnitsInferenceImplicitsTreeAnnotator(),
                new UnitsInferenceTreeAnnotator(
                        this, realChecker, realTypeFactory, variableAnnotator, slotManager));
    }

    protected final class UnitsInferenceImplicitsTreeAnnotator extends ImplicitsTreeAnnotator {
        // Programmatically set the qualifier implicits
        public UnitsInferenceImplicitsTreeAnnotator() {
            super(UnitsInferenceAnnotatedTypeFactory.this);

            // set BOTTOM for null literals
            addLiteralKind(LiteralKind.NULL, unitsRepUtils.BOTTOM);

            // set DIMENSIONLESS for the non number literals
            addLiteralKind(LiteralKind.STRING, unitsRepUtils.DIMENSIONLESS);
            addLiteralKind(LiteralKind.CHAR, unitsRepUtils.DIMENSIONLESS);
            addLiteralKind(LiteralKind.BOOLEAN, unitsRepUtils.DIMENSIONLESS);

            // TODO: set BOTTOM as the implicit qualifier for lower bounds? Its nice to
            // infer a bound which is the current mode.

            // in inference mode, we do not implicitly set dimensionless for the number
            // literals as we want to treat them as polymorphic. A "cast" is inferred for
            // each literal
        }
    }

    private final class UnitsInferenceTreeAnnotator extends InferenceTreeAnnotator {
        // TODO: per design of InferenceTreeAnnotator, this code should be moved into
        // UnitsVariableAnnotator if it performs deep traversal

        public UnitsInferenceTreeAnnotator(
                InferenceAnnotatedTypeFactory atypeFactory,
                InferrableChecker realChecker,
                AnnotatedTypeFactory realAnnotatedTypeFactory,
                VariableAnnotator variableAnnotator,
                SlotManager slotManager) {
            super(
                    atypeFactory,
                    realChecker,
                    realAnnotatedTypeFactory,
                    variableAnnotator,
                    slotManager);
        }

        // ====== generate variable slots for static final constants such as Math.PI and Math.E

        // For when the constants are directly used via static import: "PI"
        @Override
        public Void visitIdentifier(IdentifierTree tree, AnnotatedTypeMirror atm) {
            super.visitIdentifier(tree, atm);
            generateVarSlotForStaticFinalConstants(tree, tree.getName(), atm);
            return null;
        }

        // For when the constants are used via Class.Constant: "Math.PI"
        @Override
        public Void visitMemberSelect(MemberSelectTree tree, AnnotatedTypeMirror atm) {
            super.visitMemberSelect(tree, atm);
            generateVarSlotForStaticFinalConstants(tree, tree.getIdentifier(), atm);
            return null;
        }

        // Generate a variable slot for a static final constant only if it
        // isn't already annotated in source or in a stub with a non-dimensionless unit
        private void generateVarSlotForStaticFinalConstants(
                Tree tree, Name name, AnnotatedTypeMirror atm) {
            // The element being accessed: F in "X.F" or "F" depending on static import
            Element member = TreeUtils.elementFromTree(tree);
            // // The class declaring element: X in "X.F" or "F" depending on static import
            // TypeElement declaringClass = ElementUtils.enclosingClass(member);
            // boolean isUnitsToolsConstant = TypesUtils.isDeclaredOfName(
            // declaringClass.asType(), UnitsTools.class.getCanonicalName());

            // the member must be a static final program constant
            if (ElementUtils.isStatic(member)
                    && ElementUtils.isFinal(member)
                    && ElementUtils.isCompileTimeConstant(member)) {

                AnnotationMirror am = atm.getEffectiveAnnotationInHierarchy(getVarAnnot());
                if (am != null) {
                    Slot slot = slotManager.getSlot(am);
                    boolean fromByteCode = ElementUtils.isElementFromByteCode(member);

                    // System.err.println(" member: " + member);
                    // System.err.println(" am: " + am);
                    // System.err.println(" fromByteCode: " + fromByteCode);
                    // System.err.println(" slot.isVariable(): " + slot.isVariable());
                    // System.err.println(" isDimensionless: " + AnnotationUtils.areSame(
                    // ((ConstantSlot) slot).getValue(), unitsRepUtils.DIMENSIONLESS));

                    // if member is from source code, it must be unannotated
                    // if member is from byte code, it must not be annotated with a
                    // non-dimensionless unit
                    if ((!fromByteCode && slot.isVariable())
                            || (fromByteCode
                                    && slot.isConstant()
                                    && AnnotationUtils.areSame(
                                            ((ConstantSlot) slot).getValue(),
                                            unitsRepUtils.DIMENSIONLESS))) {
                        // Generate a fresh variable for inference
                        AnnotationLocation loc =
                                VariableAnnotator.treeToLocation(atypeFactory, tree);
                        VariableSlot varSlot = slotManager.createVariableSlot(loc);
                        atm.replaceAnnotation(slotManager.getAnnotation(varSlot));
                    }
                }
            }
        }

        // ====== handle polymorphic returns in constructors and methods

        // see if given annotation mirror is the VarAnnot versions of @PolyUnit and
        // @PolyAll
        private boolean isPolyAnnotation(AnnotationMirror annot) {
            Slot slot = slotManager.getSlot(annot);
            if (slot.isConstant()) {
                AnnotationMirror constant = ((ConstantSlot) slot).getValue();
                return InferenceQualifierHierarchy.isPolymorphic(constant);
            }
            return false;
        }

        // based on InferenceATF.constructorFromUse()
        private boolean isConstructorDeclaredWithPolymorphicReturn(NewClassTree newClassTree) {
            final ExecutableElement constructorElem = TreeUtils.constructor(newClassTree);
            final AnnotatedTypeMirror constructorReturnType = fromNewClass(newClassTree);
            final AnnotatedExecutableType constructorType =
                    AnnotatedTypes.asMemberOf(
                            types,
                            UnitsInferenceAnnotatedTypeFactory.this,
                            constructorReturnType,
                            constructorElem);

            // if any of the annotations on the return type of the constructor is a
            // polymorphic annotation, return true
            for (AnnotationMirror annot : constructorType.getReturnType().getAnnotations()) {
                if (isPolyAnnotation(annot)) {
                    return true;
                }
            }

            return false;
        }

        // based on InferenceATF.methodFromUse()
        private boolean isMethodDeclaredWithPolymorphicReturn(
                MethodInvocationTree methodInvocationTree) {
            final ExecutableElement methodElem = TreeUtils.elementFromUse(methodInvocationTree);
            // final AnnotatedExecutableType methodType = getAnnotatedType(methodElem);

            final ExpressionTree methodSelectExpression = methodInvocationTree.getMethodSelect();
            final AnnotatedTypeMirror receiverType;
            if (methodSelectExpression.getKind() == Tree.Kind.MEMBER_SELECT) {
                receiverType =
                        getAnnotatedType(
                                ((MemberSelectTree) methodSelectExpression).getExpression());
            } else {
                receiverType = getSelfType(methodInvocationTree);
            }

            final AnnotatedExecutableType methodOfReceiver =
                    AnnotatedTypes.asMemberOf(
                            types,
                            UnitsInferenceAnnotatedTypeFactory.this,
                            receiverType,
                            methodElem);

            // if any of the annotations on the return type of the constructor is a
            // polymorphic annotation, return true
            for (AnnotationMirror annot : methodOfReceiver.getReturnType().getAnnotations()) {
                if (isPolyAnnotation(annot)) {
                    return true;
                }
            }

            return false;
        }

        @Override
        public Void visitNewClass(NewClassTree newClassTree, AnnotatedTypeMirror atm) {
            // Call super to replace polymorphic annotations with fresh variable slots
            super.visitNewClass(newClassTree, atm);

            /*
             * given   @m Clazz x = new Clazz(param)   where the constructor is
             * polymorphic: @Poly Clazz(@Poly arg)
             *
             * without the fix below, the constraints are:
             *
             * @1 <: @3
             * @2 <: @3
             * @1 <: @m
             *
             * inserted as @m Clazz x = new @1 Clazz(@2 param)
             * @3 is not inserted
             *
             * this isn't sufficient, as there is no requirement that @2 <: @m
             * in turn, it fails in type checking as the LUB of @1 and @2 can be a supertype of @m
             *
             * with the fix below, the constraints are:
             *
             * @1 <: @3
             * @2 <: @3
             * @3 <: @m
             *
             * inserted as @m Clazz x = new @1 Clazz(@2 param)
             */

            if (isConstructorDeclaredWithPolymorphicReturn(newClassTree)) {
                // For a call "new @m Clazz(@m arg)" on a polymorphic constructor
                // "@Poly Clazz(@Poly param)" we have the following annotations:

                // 1) the variable slot generated for the polymorphic declared return type
                VariableSlot varSlotForPolyReturn =
                        variableAnnotator.getOrCreatePolyVar(newClassTree);
                // disable insertion of polymorphic return variable slot
                varSlotForPolyReturn.setInsertable(false);

                // 2) the call site return type: "@m" in "new @m Clazz(...)"
                VariableSlot callSiteReturnVarSlot = slotManager.getVariableSlot(atm);

                // Create a subtype constraint: callSiteReturnVarSlot <: varSlotForPolyReturn
                // since after annotation insertion, the varSlotForPolyReturn is conceptually a
                // cast of the newly created object:
                // "(@varSlotForPolyReturn Clazz) new @m Clazz(...)"
                constraintManager.addSubtypeConstraint(callSiteReturnVarSlot, varSlotForPolyReturn);

                // Replace the slot/annotation in the atm (callSiteReturnVarSlot) with the
                // varSlotForPolyReturn for upstream analysis
                atm.replaceAnnotation(slotManager.getAnnotation(varSlotForPolyReturn));
            }

            return null;
        }

        @Override
        public Void visitMethodInvocation(
                MethodInvocationTree methodInvocationTree, AnnotatedTypeMirror atm) {
            super.visitMethodInvocation(methodInvocationTree, atm);

            if (isMethodDeclaredWithPolymorphicReturn(methodInvocationTree)) {
                VariableSlot varSlotForPolyReturn =
                        variableAnnotator.getOrCreatePolyVar(methodInvocationTree);
                // disable insertion of polymorphic return variable slot
                varSlotForPolyReturn.setInsertable(false);
            }

            return null;
        }
    }
}
