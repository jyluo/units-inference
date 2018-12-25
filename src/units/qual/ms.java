package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A millisecond.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@UnitsAlias(
    prefixExponent = -3,
    baseUnitComponents = {@BUC(unit = s.class, exponent = 1)}
)
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface ms {}
