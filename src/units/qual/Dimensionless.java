package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A dimensionless "unit".
 *
 * @checker_framework.manual #units-checker Units Checker
 */
// @SubtypeOf(UnknownUnits.class)
// @DefaultFor({
// // exceptions are always dimensionless
// EXCEPTION_PARAMETER,
// // most user classes are dimensionless, and when used as a local reference there will be
// // many type.invalid errors, this is a better default, where any variable that should be
// // refined can be tagged UnknownUnits
// LOCAL_VARIABLE, // this somehow also applies to enhanced for loop variables
// RESOURCE_VARIABLE, PARAMETER,})
// @ImplicitFor(literals = {INT, LONG, FLOAT, DOUBLE, BOOLEAN, CHAR, STRING}, // not sure that
// literals
// // need to be impliclty
// // declared
// typeNames = {Throwable.class, Exception.class, Class.class})
@UnitsAlias(baseUnits = {})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface Dimensionless {}
