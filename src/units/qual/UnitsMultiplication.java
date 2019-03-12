package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Meta-annotation for declaring that a method should be type checked as an arithmetic
 * multiplication.
 *
 * <p>Index convention: -1 is method return, 0 is the formal {@code this} parameter, and 1 to N are
 * the rest of the formal parameters in the order they are declared.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
public @interface UnitsMultiplication {

    /** Index of the result */
    int res();

    /** Index of the left operand */
    int larg();

    /** Index of the right operand */
    int rarg();
}
