import units.UnitsTools;
import units.qual.*;

class FlowRefinement {

    void methodLocalFlowSensitiveRefinement() {
        @deg double degrees = 45.0 * UnitsTools.deg;

        // temp is refined to @rad (radians) during the assignment
        double temp = Math.toRadians(degrees);
        System.out.println("angle in radians: " + temp);

        // temp is refined to @Dimensionless during the assignment
        temp = Math.sin(temp);
        System.out.println("sine of angle: " + temp);

        // Math.cos() requires the argument to be in the unit of radians
        // :: error: (argument.type.incompatible)
        temp = Math.cos(temp);
    }
}
