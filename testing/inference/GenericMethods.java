import units.qual.*;

class GenericMethods {

    public <T> T ID(T param){
        return param;
    }

    public <T extends Number> T IDTwo(T param){
        return param;
    }

    public <T> String mObject(T param){
        return param.toString() + param;
    }

    // Issue: https://github.com/opprop/checker-framework-inference/issues/170
    // public <T extends Integer> Integer mInteger(T param){
    //     return param + param;
    // }

}