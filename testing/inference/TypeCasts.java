import units.qual.*;

class TypeCasts {

    @m Integer d = (@m int) 10;

    public void Main() {
        // :: fixable-error: (assignment.type.incompatible)
        @m int k = (int) 10.0f;
        // the annoyance of the solution here is that we get something like the following:
        // @m int k = (@VarAnnot(14) int) ((@VarAnnot(13) float) (10.0f));
        // in turn:
        // @m int k = (@m int) ((@m float) (10.0f));
        // it seems a cast is always injected for each number literal

        int l = (int) 20.0f;

        // :: fixable-error: (assignment.type.incompatible)
        @s int m = l;
    }
}