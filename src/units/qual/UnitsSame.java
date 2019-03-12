package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Repeatable;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Meta-annotation for declaring that certain parameters or return types of a method must be the
 * same unit.
 *
 * <p>Index convention: -1 is method return, 0 is the formal {@code this} parameter, and 1 to N are
 * the rest of the formal parameters in the order they are declared.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@Documented
@Repeatable(UnitsSames.class)
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
public @interface UnitsSame {

    /** Index of the first operand */
    int fst();

    /** Index of the second operand */
    int snd();
}
