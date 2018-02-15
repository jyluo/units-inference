package units;

import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.qual.StubFiles;
import checkers.inference.BaseInferrableChecker;
import checkers.inference.InferenceChecker;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.model.ConstraintManager;

@StubFiles({"JavaBoxedPrimitives.astub", "JavaLangSystem.astub"})
public class UnitsChecker extends BaseInferrableChecker {

    @Override
    public void initChecker() {
        super.initChecker();
    }

    @Override
    public UnitsVisitor createVisitor(InferenceChecker iChecker, BaseAnnotatedTypeFactory factory,
            boolean infer) {
        return new UnitsVisitor(this, iChecker, factory, infer);
    }

    @Override
    public UnitsAnnotatedTypeFactory createRealTypeFactory() {
        return new UnitsAnnotatedTypeFactory(this);
    }

    // @Override
    // public CFTransfer createInferenceTransferFunction(InferenceAnalysis analysis) {
    // return new InferenceTransfer(analysis);
    // }

    @Override
    public UnitsInferenceAnnotatedTypeFactory createInferenceATF(InferenceChecker inferenceChecker,
            InferrableChecker realChecker, BaseAnnotatedTypeFactory realTypeFactory,
            SlotManager slotManager, ConstraintManager constraintManager) {
        return new UnitsInferenceAnnotatedTypeFactory(
                inferenceChecker, realTypeFactory, realChecker, slotManager, constraintManager);
    }

    // @Override
    // public boolean isConstant(Tree node) {
    // System.out.println(" UnitsChecker isConstant " + node);
    // return super.isConstant(node);
    // }
    //
    @Override
    public boolean isInsertMainModOfLocalVar() {
        return true;
    }

    @Override
    public boolean withCombineConstraints() {
        return false;
    }

    /*
     * defined in base inferrable checker
     * 
     * @Override public Set<Class<? extends Annotation>> dependentAnnotationsForJaifInsertion() {
     * return Collections.emptySet(); }
     * 
     * // in InferenceMain.writeJaif() add this just above getting the supported qualifiers anno
     * classes // TODO: this implementation requires each checker to state the dependent //
     * annotations, if they are used as subfields of an annotation. // it is better to deeps-can the
     * annotation definition of supported qualifiers and // reflectively load the annotation class
     * into this set. for (Class<? extends Annotation> annotation : realChecker
     * .dependentAnnotationsForJaifInsertion()) { annotationClasses.add(annotation); }
     * 
     */

    // @Override
    // public Set<Class<? extends Annotation>> dependentAnnotationsForJaifInsertion() {
    // Set<Class<? extends Annotation>> additionalAnnos = new HashSet<>();
    // additionalAnnos.add(BaseUnit.class);
    // return additionalAnnos;
    // }
}
