import units.UnitsTools;
import units.qual.*;

class UnitsToolsMethods {
    void m() {
        // :: fixable-error: (assignment.type.incompatible)
        @s int seconds = 10;

        @ms int milliseconds = UnitsTools.secondsToMilliSeconds(seconds);

        int millisecondsTwo = UnitsTools.secondsToMilliSeconds(seconds);
    }
}
