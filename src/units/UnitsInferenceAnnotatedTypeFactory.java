package units;

import java.lang.annotation.Annotation;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.VariableElement;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;
import org.checkerframework.javacutil.TreeUtils;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.Tree;
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
import checkers.inference.util.CopyUtil;
import units.qual.UnitsAlias;
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
        public Void visitDeclared(AnnotatedDeclaredType adt, Tree tree) {
            // Use super to create variableSlots first
            super.visitDeclared(adt, tree);

            if (tree instanceof BinaryTree) {
                return null;
            }

            switch (tree.getKind()) {
                case VARIABLE:
                    // TODO: filter out enum? See super implementation

                    // Add an equality constraint between the varAnnot and the type qualifier
                    // declared on the variable (or default type qualifier)
                    AnnotatedTypeMirror useType = realTypeFactory.getAnnotatedType(tree);
                    ConstantSlot csUseType = variableAnnotator.createConstant(
                            useType.getAnnotationInHierarchy(UnitsUtils.UNKNOWNUNITS), tree);
                    Slot vsVarAnnot =
                            slotManager.getSlot(adt.getAnnotationInHierarchy(getVarAnnot()));
                    constraintManager.addEqualityConstraint(vsVarAnnot, csUseType);
                    break;

                default:
                    break;
            }

            return null;
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

        // @Override
        // protected Set<AnnotationMirror> findBottoms(
        // Map<AnnotationMirror, Set<AnnotationMirror>> supertypes) {
        // Set<AnnotationMirror> newBottoms = super.findBottoms(supertypes);
        // newBottoms.remove(UnitsUtils.ONTOLOGY);
        // newBottoms.add(UnitsUtils.ONTOLOGY_BOTTOM);
        //
        // //update supertypes
        // Set<AnnotationMirror> supertypesOfBtm = new HashSet<>();
        // supertypesOfBtm.add(UnitsUtils.ONTOLOGY_TOP);
        // supertypes.put(UnitsUtils.ONTOLOGY_BOTTOM, supertypesOfBtm);
        //
        // return newBottoms;
        // }

        // @Override
        // protected void finish(
        // QualifierHierarchy qualHierarchy,
        // Map<AnnotationMirror, Set<AnnotationMirror>> fullMap,
        // Map<AnnotationMirror, AnnotationMirror> polyQualifiers,
        // Set<AnnotationMirror> tops,
        // Set<AnnotationMirror> bottoms,
        // Object... args) {
        // super.finish(qualHierarchy, fullMap, polyQualifiers, tops, bottoms, args);
        //
        // // substitue ONTOLOGY with ONTOLOGY_TOP in fullMap
        // assert fullMap.containsKey(UnitsUtils.ONTOLOGY);
        // Set<AnnotationMirror> ontologyTopSupers = fullMap.get(UnitsUtils.ONTOLOGY);
        // fullMap.put(UnitsUtils.ONTOLOGY_TOP, ontologyTopSupers);
        // fullMap.remove(UnitsUtils.ONTOLOGY);
        // }
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
        public Void visitIdentifier(IdentifierTree node, AnnotatedTypeMirror identifierType) {
            System.out.println(" visitID " + node + " atm: " + identifierType);

            return super.visitIdentifier(node, identifierType);
        }
        //
        // @Override
        // public Void visitVariable(VariableTree varTree, AnnotatedTypeMirror atm) {
        //
        // System.out.println(" UIATF visitVar tree: " + varTree);
        // System.out.println(" atm: " + atm);
        // System.out.println(" modifiers: " + varTree.getModifiers());
        // System.out.println(" name: " + varTree.getName());
        // System.out.println(" name expression: " + varTree.getNameExpression());
        // System.out.println(" type: " + varTree.getType());
        // System.out.println(" init: " + varTree.getInitializer());
        //
        // VariableElement varEle = TreeUtils.elementFromDeclaration(varTree);
        //
        // System.out.println(" varEle: " + varEle);
        //
        // super.visitVariable(varTree, atm);
        //
        // System.out.println(" post atm: " + atm);
        //
        // return null;
        // }

        @Override
        public Void visitLiteral(LiteralTree literalTree, AnnotatedTypeMirror atm) {
            // TODO: refine it down to number literals

            // number literals are always dimensionless

            // Create an AM
            AnnotationMirror anno = UnitsUtils.DIMENSIONLESS; // Default for all literals
            // Create a slot
            ConstantSlot cs = variableAnnotator.createConstant(anno, literalTree);
            // Replace atm value
            atm.replaceAnnotation(cs.getValue());
            // Visit the atm with the tree
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

        // @Override
        // public Void visitNewClass(final NewClassTree newClassTree, final AnnotatedTypeMirror atm)
        // {
        // switch (UnitsUtils.determineUnitsValue(atm.getUnderlyingType())) {
        // case SEQUENCE: {
        // AnnotationMirror anno = UnitsUtils.createUnitsAnnotationByValues(processingEnv,
        // UnitsValue.SEQUENCE);
        // ConstantSlot cs = variableAnnotator.createConstant(anno, newClassTree);
        // atm.replaceAnnotation(cs.getValue());
        // }
        // break;
        //
        // case TOP:
        // default:
        // break;
        // }
        // variableAnnotator.visit(atm, newClassTree.getIdentifier());
        // return null;
        // }
        //
        // @Override
        // public Void visitNewArray(final NewArrayTree newArrayTree, final AnnotatedTypeMirror atm)
        // {
        // AnnotationMirror anno =
        // UnitsUtils.createUnitsAnnotationByValues(processingEnv, UnitsValue.SEQUENCE);
        // ConstantSlot cs = variableAnnotator.createConstant(anno, newArrayTree);
        // atm.replaceAnnotation(cs.getValue());
        // variableAnnotator.visit(atm, newArrayTree);
        // return null;
        // }
        //
        // @Override
        // public Void visitParameterizedType(final ParameterizedTypeTree param,
        // final AnnotatedTypeMirror atm) {
        // TreePath path = atypeFactory.getPath(param);
        // if (path != null) {
        // final TreePath parentPath = path.getParentPath();
        // final Tree parentNode = parentPath.getLeaf();
        // if (!parentNode.getKind().equals(Kind.NEW_CLASS)) {
        // variableAnnotator.visit(atm, param);
        // }
        // }
        // return null;
        // }
    }
}
