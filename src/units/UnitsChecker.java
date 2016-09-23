package units;

import checkers.inference.BaseInferrableChecker;
import checkers.inference.InferenceChecker;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.dataflow.InferenceAnalysis;
import checkers.inference.dataflow.InferenceTransfer;
import checkers.inference.model.ConstraintManager;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.flow.CFTransfer;

public class UnitsChecker extends BaseInferrableChecker {

  @Override
  public void initChecker() {
    super.initChecker();
  }

  @Override
  public UnitsVisitor createVisitor(
      InferenceChecker iChecker, BaseAnnotatedTypeFactory factory, boolean infer) {
    return new UnitsVisitor(this, iChecker, factory, infer);
  }

  @Override
  public UnitsAnnotatedTypeFactory createRealTypeFactory() {
    return new UnitsAnnotatedTypeFactory(this);
  }

  @Override
  public CFTransfer createInferenceTransferFunction(InferenceAnalysis analysis) {
    return new InferenceTransfer(analysis);
  }

  @Override
  public UnitsInferenceAnnotatedTypeFactory createInferenceATF(
      InferenceChecker inferenceChecker,
      InferrableChecker realChecker,
      BaseAnnotatedTypeFactory realTypeFactory,
      SlotManager slotManager,
      ConstraintManager constraintManager) {
    UnitsInferenceAnnotatedTypeFactory ontologyInferenceATF =
        new UnitsInferenceAnnotatedTypeFactory(
            inferenceChecker,
            realChecker.withCombineConstraints(),
            realTypeFactory,
            realChecker,
            slotManager,
            constraintManager);
    return ontologyInferenceATF;
  }

  @Override
  public boolean isInsertMainModOfLocalVar() {
    return true;
  }

  @Override
  public boolean withCombineConstraints() {
    return false;
  }
}
