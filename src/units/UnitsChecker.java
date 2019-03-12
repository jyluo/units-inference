package units;

import checkers.inference.BaseInferrableChecker;
import checkers.inference.InferenceChecker;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.model.ConstraintManager;
import java.lang.annotation.Annotation;
import java.util.Set;
import javax.annotation.processing.SupportedOptions;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.qual.StubFiles;

/**
 * Units Checker main class.
 *
 * <p>Supports "units" option to add support for additional individually named and externally
 * defined units, and "unitsDirs" option to add support for directories of externally defined units.
 * Directories must be well-formed paths from file system root, separated by colon (:) between each
 * directory.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@StubFiles({
    "JavaBoxedPrimitives.astub",
    "JavaIOPrintstream.astub",
    "JavaLang.astub",
    "JavaMath.astub",
    "JavaThread.astub",
    "JavaUtil.astub",
    "JavaUtilConcurrent.astub",
    "ExperimentsJavaAwtGeomAffineTransform.astub", // for imgscalr experiment
    "ExperimentsSunMiscUnsafe.astub", // for JLargeArrays
})
@SupportedOptions({"units", "unitsDirs"})
public class UnitsChecker extends BaseInferrableChecker {

    protected UnitsInferenceAnnotatedTypeFactory unitsIATF;

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
    public UnitsInferenceAnnotatedTypeFactory createInferenceATF(
            InferenceChecker inferenceChecker,
            InferrableChecker realChecker,
            BaseAnnotatedTypeFactory realTypeFactory,
            SlotManager slotManager,
            ConstraintManager constraintManager) {
        unitsIATF =
                new UnitsInferenceAnnotatedTypeFactory(
                        inferenceChecker,
                        realTypeFactory,
                        realChecker,
                        slotManager,
                        constraintManager);
        return unitsIATF;
    }

    @Override
    public boolean isInsertMainModOfLocalVar() {
        return true;
    }

    @Override
    public boolean withCombineConstraints() {
        return false;
    }

    @Override
    public Set<Class<? extends Annotation>> additionalAnnotationsForJaifHeaderInsertion() {
        return unitsIATF.getUnitsRepresentationUtils().surfaceUnitsSet();
    }
}
