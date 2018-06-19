package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A square meter.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@UnitsAlias({@BaseUnit(unit = "m", exponent = 2)})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface m2 {}
