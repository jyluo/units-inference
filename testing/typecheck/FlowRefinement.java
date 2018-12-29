import units.UnitsTools;
import units.qual.*;

class FlowRefinement {

    void methodLocalFlowSensitiveRefinement() {
        @deg double d = 45.0 * UnitsTools.deg;

        double temp = Math.toRadians(d);  // temp is refined to @rad during the assignment

        System.out.println("angle in radians: " + temp);

        temp = Math.sin(temp);  // temp is refined to @Dimensionless during the assignment

        System.out.println("sine of angle: " + temp);

        // :: error: (argument.type.incompatible)
        temp = Math.cos(temp);  // Math.cos() requires the argument to be in the unit of radians
    }
}
