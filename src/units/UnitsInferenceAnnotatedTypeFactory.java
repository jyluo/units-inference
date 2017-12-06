package units;

import java.lang.annotation.Annotation;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationUtils;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
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
import units.qual.UnitsAlias;
import units.util.UnitsUtils;

public class UnitsInferenceAnnotatedTypeFactory extends InferenceAnnotatedTypeFactory {

    public UnitsInferenceAnnotatedTypeFactory(InferenceChecker inferenceChecker,
            boolean withCombineConstraints, BaseAnnotatedTypeFactory realTypeFactory,
            InferrableChecker realChecker, SlotManager slotManager,
            ConstraintManager constraintManager) {
        super(inferenceChecker, withCombineConstraints, realTypeFactory, realChecker, slotManager,
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

//        // load all the external units
//        loadAllExternalUnits();
//
//        // copy all loaded external Units to qual set
//        qualSet.addAll(externalQualsMap.values());

        return qualSet;
    }
    
    @Override
    public AnnotationMirror aliasedAnnotation(AnnotationMirror anno) {
        for (AnnotationMirror metaAnno : anno.getAnnotationType().asElement().getAnnotationMirrors()) {
            if(AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)) {
                
                System.out.println(" aliasing " + anno);
                
                Map<String, Integer> exponents = new TreeMap<>();
                exponents.put("m", 1);
                exponents.put("s", 1);
                
                return UnitsUtils.createInternalUnit("dummy", 1, exponents);
            }
        }
        
        return super.aliasedAnnotation(anno);
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
        
//        @Override
//        public Void visitIdentifier(IdentifierTree node, AnnotatedTypeMirror identifierType) {
//            System.out.println(" visitID " + node +  " atm: " + identifierType);
//            
//            return super.visitIdentifier(node, identifierType);
//        }

        @Override
        public Void visitVariable(VariableTree varTree, AnnotatedTypeMirror atm) {
            
            System.out.println(" UIATF visitVar tree: " + varTree);
            System.out.println("      atm: " + atm);
            
            super.visitVariable(varTree, atm);
            
            System.out.println(" post atm: " + atm);
            
            return null;
        }
        
//        @Override
//        public Void visitLiteral(LiteralTree literalTree, AnnotatedTypeMirror atm) {
//            // TODO: refine it down to number literals
//
//            // number literals are always dimensionless
//
//            // Create an AM
//            AnnotationMirror anno = UnitsUtils.DIMENSIONLESS; // Default for all literals
//            // Create a slot
//            ConstantSlot cs = variableAnnotator.createConstant(anno, literalTree);
//            // Replace atm value
//            atm.replaceAnnotation(cs.getValue());
//            // Visit the atm with the tree
//            variableAnnotator.visit(atm, literalTree);
//            return null;
//        }

        @Override
        public Void visitBinary(BinaryTree binaryTree, AnnotatedTypeMirror atm) {
            // Overrides only required if i want to replace a varslot with constant slot
            // varAnnotator adds varSlots, call it sometimes, see InfTreeANnotator

            Map<String, Integer> exponents = new TreeMap<>();
            exponents.put("m", 1);
            exponents.put("s", 1);

            AnnotationMirror anno = UnitsUtils.createInternalUnit("dummy", 1, exponents);
            ConstantSlot cs = variableAnnotator.createConstant(anno, binaryTree);
            atm.replaceAnnotation(cs.getValue());
            variableAnnotator.visit(atm, binaryTree);
            return null;
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
