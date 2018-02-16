package units;

import java.lang.annotation.Annotation;
import java.util.HashSet;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotationClassLoader;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.VariableTree;
import checkers.inference.InferenceAnnotatedTypeFactory;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceQualifierHierarchy;
import checkers.inference.InferenceTreeAnnotator;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import units.representation.UnitsRepresentationUtils;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.VariableSlot;

public class UnitsInferenceAnnotatedTypeFactory extends InferenceAnnotatedTypeFactory {

    public UnitsInferenceAnnotatedTypeFactory(InferenceChecker inferenceChecker,
            BaseAnnotatedTypeFactory realTypeFactory, InferrableChecker realChecker,
            SlotManager slotManager, ConstraintManager constraintManager) {
        super(inferenceChecker, false, realTypeFactory, realChecker, slotManager,
                constraintManager);
        UnitsRepresentationUtils.getInstance(processingEnv, elements);
        postInit();
    }

    @Override
    protected AnnotationClassLoader createAnnotationClassLoader() {
        // Use the Units Annotated Type Loader instead of the default one
        return new UnitsAnnotationClassLoader(checker);
    }

    @Override
    protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
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
        // TODO: cache results
        // TODO: alias empty @units.qual.UnitsInternal to instantiated dimensionless
        // TODO: alias dimensionless?
        AnnotationMirror result = realTypeFactory.aliasedAnnotation(anno);
        // System.out.println(" === Aliasing: " + anno.toString() + " ==> " + result);

        if (result == null) {
            result = super.aliasedAnnotation(anno);
        }
        return result;
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
        public void handleBinaryTree(AnnotatedTypeMirror atm, BinaryTree node) {
            // Super creates an LUB constraint by default, we create an VariableSlot here instead
            // for the result of the binary op and create LUB constraint in tree annotator.
            if (treeToVarAnnoPair.containsKey(node)) {
                atm.replaceAnnotations(treeToVarAnnoPair.get(node).second);
            } else {
                VariableSlot result = slotManager.getVariableSlot(atm);
                if (result == null) {
                    // if we want the result to be inserted into source, use this version:
                    // result = slotManager.createVariableSlot(treeToLocation(binaryTree));

                    // create a non-insertable var slot
                    AnnotatedTypeMirror lhsATM =
                            inferenceTypeFactory.getAnnotatedType(node.getLeftOperand());
                    AnnotatedTypeMirror rhsATM =
                            inferenceTypeFactory.getAnnotatedType(node.getRightOperand());
                    VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
                    VariableSlot rhs = slotManager.getVariableSlot(rhsATM);

                    // // if there's no var slots available for LHS or RHS, replace with a constant
                    // // slot of the default or implicit annotation computed from real type factory
                    // if (lhs == null) {
                    // lhs = slotManager.createConstantSlot(
                    // realTypeFactory.getAnnotatedType(node.getLeftOperand())
                    // .getAnnotationInHierarchy(UnitsRepresentationUtils.UNKNOWNUNITS));
                    // }
                    // if (rhs == null) {
                    // rhs = slotManager.createConstantSlot(
                    // realTypeFactory.getAnnotatedType(node.getRightOperand())
                    // .getAnnotationInHierarchy(UnitsRepresentationUtils.UNKNOWNUNITS));
                    // }

                    result = slotManager.createArithmeticVariableSlot(
                            ArithmeticOperationKind.fromTreeKind(node.getKind()), lhs, rhs);
                }

                AnnotationMirror resultAM = slotManager.getAnnotation(result);
                atm.clearAnnotations();
                atm.replaceAnnotation(resultAM);

                Set<AnnotationMirror> resultSet = AnnotationUtils.createAnnotationSet();
                resultSet.add(resultAM);

                final Pair<VariableSlot, Set<? extends AnnotationMirror>> varATMPair =
                        Pair.<VariableSlot, Set<? extends AnnotationMirror>>of(
                                slotManager.getVariableSlot(atm), resultSet);
                treeToVarAnnoPair.put(node, varATMPair);
            }
        }

        // private VariableSlot getOrCreateSlot(AnnotatedTypeMirror atm, Tree tree) {
        // // create a var slot from scratch if the atm doesn't have one.
        // VariableSlot slot = slotManager.getVariableSlot(atm);
        // if (slot == null) {
        // slot = slotManager.createVariableSlot(treeToLocation(tree));
        // // slot = slotManager.getVariableSlot(atm);
        // assert slot != null;
        // }
        // return slot;
        // }
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
        UnitsRepresentationUtils.getInstance(processingEnv, elements);
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

            boolean hasExplicitUnitsAnnotation = false;
            AnnotatedTypeMirror realATM = realTypeFactory.getAnnotatedType(varTree);

            // TODO: aliases and base unit annos used in variable declarations don't work right now
            for (AnnotationMirror anno : realATM.getExplicitAnnotations()) {
                if (UnitsRepresentationUtils.isUnitsAnnotation(realTypeFactory, anno)) {
                    hasExplicitUnitsAnnotation = true;
                    break;
                }
            }

            if (hasExplicitUnitsAnnotation) {
                // Create a ConstantSlot for the explicit annotation
                AnnotationMirror realAnno =
                        realATM.getAnnotationInHierarchy(UnitsRepresentationUtils.UNKNOWNUNITS);
                ConstantSlot declaredAnnoSlot = variableAnnotator.createConstant(realAnno, varTree);
                // Get the VariableSlot generated for the variable
                VariableSlot varAnnotSlot = slotManager.getVariableSlot(atm);
                // Add Equality constraint between the VariableSlot and the ConstantSlot
                constraintManager.addEqualityConstraint(varAnnotSlot, declaredAnnoSlot);
            }

            return null;
        }

        // @Override
        // public Void visitLiteral(LiteralTree literalTree, AnnotatedTypeMirror atm) {
        // // NOTE: generally inference should not apply defaults, and instead create slots.
        // // In units, this results in literals being casted into a unit type.
        // // TODO: Should create a post-inference code-fix tool to replace casts with UnitsTools
        // multiplication.
        //
        // // The code here applies the default type for literals, which is not what we want
        // AnnotatedTypeMirror realATM = realTypeFactory.getAnnotatedType(literalTree);
        // AnnotationMirror realAnno = realATM.getAnnotationInHierarchy(UnitsRepresentationUtils.UNKNOWNUNITS);
        // ConstantSlot cs = variableAnnotator.createConstant(realAnno, literalTree);
        // atm.replaceAnnotation(cs.getValue());
        // variableAnnotator.visit(atm, literalTree);
        // return null;
        // }

        @Override
        public Void visitBinary(BinaryTree node, AnnotatedTypeMirror atm) {
            // From super:
            // Unary trees and compound assignments (x++ or x +=y) get desugared
            // by dataflow to be x = x + 1 and x = x + y.
            // Dataflow will then look up the types of the binary operations (x + 1) and (y + 1)
            //
            // InferenceTransfer currently sets the value of a compound assignment or unary
            // to be the just the type of the variable.
            // So, the type returned from this for desugared trees is not used.
            // We don't create a constraint to reduce confusion
            if (realTypeFactory.getPath(node) == null) {
                // Desugared tree's don't have paths.
                // There currently is some case that we are missing that requires us to annotate
                // these.
                return null;
            }

            // visit via variableAnnotator to create a ArithmeticVariableSlot for the result atm
            variableAnnotator.visit(atm, node);

            Kind kind = node.getKind();
            AnnotatedTypeMirror lhsATM = atypeFactory.getAnnotatedType(node.getLeftOperand());
            AnnotatedTypeMirror rhsATM = atypeFactory.getAnnotatedType(node.getRightOperand());
            VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
            VariableSlot rhs = slotManager.getVariableSlot(rhsATM);
            VariableSlot result = slotManager.getVariableSlot(atm);

            // if there's no var slots available for LHS or RHS, replace with a constant
            // slot of the default or implicit annotation computed from real type factory
            if (lhs == null) {
                lhs = slotManager
                        .createConstantSlot(realTypeFactory.getAnnotatedType(node.getLeftOperand())
                                .getAnnotationInHierarchy(UnitsRepresentationUtils.UNKNOWNUNITS));
            }
            if (rhs == null) {
                rhs = slotManager
                        .createConstantSlot(realTypeFactory.getAnnotatedType(node.getRightOperand())
                                .getAnnotationInHierarchy(UnitsRepresentationUtils.UNKNOWNUNITS));
            }

            // TODO: can compute direct results for Constant-Constant here or do it at inference
            // currently computed at inference
            ArithmeticOperationKind opKind = ArithmeticOperationKind.fromTreeKind(node.getKind());
            if (opKind != null) {
                constraintManager.addArithmeticConstraint(opKind, lhs, rhs, result);
            } else {
                // null means an unsupported arithmetic operation
                // Create LUB constraint by default
                // TODO: formally define LUBConstraint in constraintManager
                constraintManager.addSubtypeConstraint(lhs, result);
                constraintManager.addSubtypeConstraint(rhs, result);
            }
            atm.clearAnnotations();
            atm.addAnnotation(slotManager.getAnnotation(result));

            return null;
        }

        @Override
        public Void visitTypeCast(TypeCastTree typeCast, AnnotatedTypeMirror atm) {
            super.visitTypeCast(typeCast, atm);

            boolean hasExplicitUnitsAnnotation = false;
            AnnotatedTypeMirror realATM = realTypeFactory.getAnnotatedType(typeCast);

            // TODO: aliases and base unit annos used in variable declarations don't work right now
            for (AnnotationMirror anno : realATM.getAnnotations()) {
                if (UnitsRepresentationUtils.isUnitsAnnotation(realTypeFactory, anno)) {
                    hasExplicitUnitsAnnotation = true;
                    break;
                }
            }

            if (hasExplicitUnitsAnnotation) {
                // Create a ConstantSlot for the explicit annotation
                AnnotationMirror realAnno =
                        realATM.getAnnotationInHierarchy(UnitsRepresentationUtils.UNKNOWNUNITS);
                ConstantSlot declaredAnnoSlot =
                        variableAnnotator.createConstant(realAnno, typeCast);
                // Get the VariableSlot generated for the variable
                VariableSlot varAnnotSlot = slotManager.getVariableSlot(atm);
                // Add Equality constraint between the VariableSlot and the ConstantSlot
                constraintManager.addEqualityConstraint(varAnnotSlot, declaredAnnoSlot);
            }

            return null;
        }

        //
        // private VariableSlot getOrCreateSlot(AnnotatedTypeMirror atm, Tree tree) {
        // // create a var slot from scratch if the atm doesn't have one.
        // VariableSlot slot = slotManager.getVariableSlot(atm);
        // if (slot == null) {
        // slot = slotManager.createVariableSlot(VariableAnnotator.treeToLocation(atypeFactory,
        // tree));
        // // slot = slotManager.getVariableSlot(atm);
        // assert slot != null;
        // }
        // return slot;
        // }
    }
}
