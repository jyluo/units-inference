package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Pixel per inch.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@UnitsAlias({@BaseUnit(unit = "px", exponent = 1), @BaseUnit(unit = "in", exponent = -1)})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface pxPERin {
}
