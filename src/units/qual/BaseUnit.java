package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Documented
@Retention(RetentionPolicy.RUNTIME)
public @interface BaseUnit {
    // TODO: replace with Class<? extends Annotation>, makes it more type safe
    String unit() default "none";

    int exponent() default 0;
}
