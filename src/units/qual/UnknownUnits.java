package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * UnknownUnits is the top type of the type hierarchy.
 *
 * @checker_framework.manual #units-checker Units Checker
 */
// @DefaultQualifierInHierarchyInUncheckedCode()
// @DefaultInUncheckedCodeFor({TypeUseLocation.PARAMETER, TypeUseLocation.UPPER_BOUND})
// @DefaultFor({
// // LOCAL_VARIABLE, // for flow based type refinement in the body of methods
// // EXCEPTION_PARAMETER, // exceptions are always top
// IMPLICIT_UPPER_BOUND, // <T>, so that T can take on any type in usage
// })
@UnitsAlias(baseUnitComponents = {})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER}) // ElementType.TYPE,
public @interface UnknownUnits {}
