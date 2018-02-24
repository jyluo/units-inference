package units;

import java.lang.annotation.Annotation;
import java.util.HashSet;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFormatter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotationClassLoader;
import org.checkerframework.framework.type.DefaultAnnotatedTypeFormatter;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.AnnotationFormatter;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.TypeCastTree;
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
import checkers.inference.model.VariableSlot;
import units.representation.UnitsRepresentationUtils;

public class UnitsInferenceAnnotatedTypeFactory extends InferenceAnnotatedTypeFactory {
    // static reference to the singleton instance
    protected static UnitsRepresentationUtils unitsRepUtils;

    public UnitsInferenceAnnotatedTypeFactory(InferenceChecker inferenceChecker,
            BaseAnnotatedTypeFactory realTypeFactory, InferrableChecker realChecker,
            SlotManager slotManager, ConstraintManager constraintManager) {
        super(inferenceChecker, false, realTypeFactory, realChecker, slotManager,
                constraintManager);

        // Should already be initialized in the real ATF
        unitsRepUtils = UnitsRepresentationUtils.getInstance();
        // and it should already have some base units
        assert !unitsRepUtils.baseUnits().isEmpty();

        postInit();
    }

    @Override
    protected AnnotationClassLoader createAnnotationClassLoader() {
        // Use the Units Annotated Type Loader instead of the default one
        return new UnitsAnnotationClassLoader(checker);
    }

    // In Inference ATF, this returns the set of real qualifiers
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

        // create internal use annotation mirrors using the base units that have been initialized.
        // must be called here as other methods called within ATF.postInit() requires the annotation
        // mirrors
        unitsRepUtils.postInit();

        return qualSet;
    }

    // In Inference ATF, this returns the alias for a given real qualifier
    @Override
    public AnnotationMirror aliasedAnnotation(AnnotationMirror anno) {
        // TODO: cache results
        AnnotationMirror result = realTypeFactory.aliasedAnnotation(anno);
        // System.out.println(" === Aliasing: " + anno.toString() + " ==> " + result);

        if (result == null) {
            result = super.aliasedAnnotation(anno);
        }
        return result;
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
    public VariableAnnotator createVariableAnnotator() {
        return new UnitsVariableAnnotator(this, realTypeFactory, realChecker, slotManager,
                constraintManager);
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
            // for the result of the binary op and create LUB constraint in units visitor.
            if (treeToVarAnnoPair.containsKey(node)) {
                atm.replaceAnnotations(treeToVarAnnoPair.get(node).second);
            } else {
                // grab slots for the component (only for lub slot)
                AnnotatedTypeMirror lhsATM =
                        inferenceTypeFactory.getAnnotatedType(node.getLeftOperand());
                AnnotatedTypeMirror rhsATM =
                        inferenceTypeFactory.getAnnotatedType(node.getRightOperand());
                VariableSlot lhs = slotManager.getVariableSlot(lhsATM);
                VariableSlot rhs = slotManager.getVariableSlot(rhsATM);

                // create varslot for the result of the binary tree computation
                VariableSlot result;
                switch (node.getKind()) {
                    case PLUS:
                    case MINUS:
                    case MULTIPLY:
                    case DIVIDE:
                    case REMAINDER:
                        result = slotManager.createArithmeticVariableSlot(treeToLocation(node));
                        break;
                    default:
                        // TODO: replace with LUBSlot pending mier's PR
                        result = slotManager.createCombVariableSlot(lhs, rhs);
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
                        Pair.<VariableSlot, Set<? extends AnnotationMirror>>of(
                                slotManager.getVariableSlot(atm), resultSet);
                treeToVarAnnoPair.put(node, varATMPair);
            }
        }
    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        UnitsRepresentationUtils.getInstance(processingEnv, elements);
        return new ListTreeAnnotator(new ImplicitsTreeAnnotator(this),
                new UnitsInferenceTreeAnnotator(this, realChecker, realTypeFactory,
                        variableAnnotator, slotManager));
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

            AnnotatedTypeMirror realATM = realTypeFactory.getAnnotatedType(varTree);

            // TODO: back mapping of inference result annots to surface units

            // If there is a units annotation, then retrieve it, normalize it, create a constant
            // slot for it, and an equality constraint between the constant slot and the VarAnnot
            // generated for the ATM
            AnnotationMirror realUnitsAnno = realATM.getAnnotationInHierarchy(unitsRepUtils.TOP);
            if (realUnitsAnno != null) {
                // Fill in any missing base units
                realUnitsAnno = unitsRepUtils.fillMissingBaseUnits(realUnitsAnno);
                // Create a ConstantSlot for the explicit annotation
                ConstantSlot constSlot = variableAnnotator.createConstant(realUnitsAnno, varTree);
                // Get the VariableSlot generated for the variable
                VariableSlot varAnnotSlot = slotManager.getVariableSlot(atm);
                // Add Equality constraint between the VariableSlot and the ConstantSlot
                constraintManager.addEqualityConstraint(varAnnotSlot, constSlot);
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
        // AnnotationMirror realAnno =
        // realATM.getAnnotationInHierarchy(UnitsRepresentationUtils.TOP);
        // ConstantSlot cs = variableAnnotator.createConstant(realAnno, literalTree);
        // atm.replaceAnnotation(cs.getValue());
        // variableAnnotator.visit(atm, literalTree);
        // return null;
        // }

        // @Override
        // public Void visitBinary(BinaryTree node, AnnotatedTypeMirror atm) {
        // // From super:
        // // Unary trees and compound assignments (x++ or x +=y) get desugared
        // // by dataflow to be x = x + 1 and x = x + y.
        // // Dataflow will then look up the types of the binary operations (x + 1) and (y + 1)
        // //
        // // InferenceTransfer currently sets the value of a compound assignment or unary
        // // to be the just the type of the variable.
        // // So, the type returned from this for desugared trees is not used.
        // // We don't create a constraint to reduce confusion
        // if (realTypeFactory.getPath(node) == null) {
        // // Desugared tree's don't have paths.
        // // There currently is some case that we are missing that requires us to annotate
        // // these.
        // return null;
        // }
        //
        // // visit via variableAnnotator to create a ArithmeticVariableSlot or LUBSlot for the
        // // result atm
        // variableAnnotator.visit(atm, node);
        //
        // return null;
        // }

        @Override
        public Void visitTypeCast(TypeCastTree tree, AnnotatedTypeMirror atm) {
            super.visitTypeCast(tree, atm);

            AnnotatedTypeMirror realATM = realTypeFactory.getAnnotatedType(tree);

            // TODO: shared logic, put in helper

            // If there is a units annotation, then retrieve it, normalize it, create a constant
            // slot for it, and an equality constraint between the constant slot and the VarAnnot
            // generated for the ATM
            AnnotationMirror realUnitsAnno = realATM.getAnnotationInHierarchy(unitsRepUtils.TOP);
            if (realUnitsAnno != null) {
                // Fill in any missing base units
                realUnitsAnno = unitsRepUtils.fillMissingBaseUnits(realUnitsAnno);
                // Create a ConstantSlot for the explicit annotation
                ConstantSlot constSlot = variableAnnotator.createConstant(realUnitsAnno, tree);
                // Get the VariableSlot generated for the variable
                VariableSlot varAnnotSlot = slotManager.getVariableSlot(atm);
                // Add Equality constraint between the VariableSlot and the ConstantSlot
                constraintManager.addEqualityConstraint(varAnnotSlot, constSlot);
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

    // for use in AnnotatedTypeMirror.toString()
    @Override
    protected AnnotatedTypeFormatter createAnnotatedTypeFormatter() {
        return new DefaultAnnotatedTypeFormatter(createAnnotationFormatter(),
                checker.hasOption("printVerboseGenerics"), checker.hasOption("printAllQualifiers"));
    }

    // for use in generating error outputs
    @Override
    protected AnnotationFormatter createAnnotationFormatter() {
        return new UnitsAnnotationFormatter(checker);
    }
}
