package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Documented
@Retention(RetentionPolicy.RUNTIME)
public @interface BaseUnit {

    // value of p in 10 ^ p as a prefix, for kilo p = 3, for milli p = -3
    int prefix() default 0;

    // TODO: replace with Class<? extends Annotation> unit();
    String unit() default "none";

    int exponent() default 0;
}
