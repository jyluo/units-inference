import units.qual.*;

class GenericMethods {

    public <T> T idOne(T param) {
        return param;
    }

    public <@UnitsBottom T extends Number> T idTwo(T param) {
        T copy = param;
        return copy;
    }

    public <T> String mStringCatOne(T param) {
        return param.toString() + param;
    }

    public <T extends Object> String mStringCatTwo(T param) {
        return param.toString() + param;
    }

    // Issue: https://github.com/opprop/checker-framework-inference/issues/170
    // public <T extends Integer> Integer mInteger(T param){
    //     return param + param;
    // }
}
