package units;

import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import com.sun.source.tree.AssignmentTree;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceVisitor;

public class UnitsVisitor extends InferenceVisitor<UnitsChecker, BaseAnnotatedTypeFactory> {

    public UnitsVisitor(UnitsChecker checker, InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory, boolean infer) {
        super(checker, ichecker, factory, infer);
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        
        System.out.println(" node > " + node);
        
        return super.visitAssignment(node, p);
    }
    
    // Slots created in ATF

    // Constraints created in Visitor

    // see
    // https://github.com/topnessman/immutability/blob/master/src/main/java/pico/inference/PICOInferenceVisitor.java


}
