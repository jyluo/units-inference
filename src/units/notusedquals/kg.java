package units.notusedquals;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import units.qual.BUC;
import units.qual.UnitsAlias;

/**
 * A kilogram.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@UnitsAlias(
    prefixExponent = 3,
    baseUnitComponents = {@BUC(unit = "g", exponent = 1)}
)
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface kg {}
