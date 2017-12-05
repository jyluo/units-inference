package units;

import checkers.inference.InferenceChecker;
import checkers.inference.InferenceVisitor;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;

public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {

    public UnitsVisitor(UnitsChecker checker, InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory, boolean infer) {
        super(checker, ichecker, factory, infer);
    }

    // Slots created in ATF

    // Constraints created in Visitor

    // see
    // https://github.com/topnessman/immutability/blob/master/src/main/java/pico/inference/PICOInferenceVisitor.java


}
