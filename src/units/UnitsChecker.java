package units;

import java.lang.annotation.Annotation;
import java.util.Set;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.qual.StubFiles;
import checkers.inference.BaseInferrableChecker;
import checkers.inference.InferenceChecker;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.model.ConstraintManager;
import units.representation.UnitsRepresentationUtils;

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
        return new UnitsInferenceAnnotatedTypeFactory(inferenceChecker, realTypeFactory,
                realChecker, slotManager, constraintManager);
    }

    // @Override
    // public boolean isConstant(Tree node) {
    // System.out.println(" UnitsChecker isConstant " + node);
    // return super.isConstant(node);
    // }
    //
    @Override
    public boolean isInsertMainModOfLocalVar() {
        return false;
    }

    @Override
    public boolean withCombineConstraints() {
        return false;
    }

    @Override
    public Set<Class<? extends Annotation>> additionalAnnotationsForJaifHeaderInsertion() {
        return UnitsRepresentationUtils.getInstance().surfaceUnitsSet();
    }
}
