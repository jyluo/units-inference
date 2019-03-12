import units.qual.*;

class BoxedNumberTypes {
    @m Number mN;
    @s Number sN;

    @m Byte mB;
    @m Short mS;
    @m Integer mI;
    @m Long mL;
    @m Float mF;
    @m Double mD;

    @s Byte sB;
    @s Short sS;
    @s Integer sI;
    @s Long sL;
    @s Float sF;
    @s Double sD;

    @m byte mb;
    @m short ms;
    @m int mi;
    @m long ml;
    @m float mf;
    @m double md;

    @s byte sb;
    @s short ss;
    @s int si;
    @s long sl;
    @s float sf;
    @s double sd;

    void testNumber() {
        mb = mN.byteValue();
        ms = mN.shortValue();
        mi = mN.intValue();
        ml = mN.longValue();
        mf = mN.floatValue();
        md = mN.doubleValue();

        // :: error: (assignment.type.incompatible)
        sb = mN.byteValue();
        // :: error: (assignment.type.incompatible)
        ss = mN.shortValue();
        // :: error: (assignment.type.incompatible)
        si = mN.intValue();
        // :: error: (assignment.type.incompatible)
        sl = mN.longValue();
        // :: error: (assignment.type.incompatible)
        sf = mN.floatValue();
        // :: error: (assignment.type.incompatible)
        sd = mN.doubleValue();
    }

    // blocked by this in stubs
    private class CustomByte {
        @PolyUnit CustomByte(@PolyUnit byte val) {}
    }

    void testByte() {
        mB = Byte.valueOf(mb);
        // mB = new Byte(mb);

        @m CustomByte cb = new CustomByte(mb);

        mb = mB.byteValue();
        ms = mB.shortValue();
        mi = mB.intValue();
        ml = mB.longValue();
        mf = mB.floatValue();
        md = mB.doubleValue();

        // :: error: (assignment.type.incompatible)
        sB = Byte.valueOf(mb);
        // :: error: (assignment.type.incompatible)
        sb = mB.byteValue();
        // :: error: (assignment.type.incompatible)
        ss = mB.shortValue();
        // :: error: (assignment.type.incompatible)
        si = mB.intValue();
        // :: error: (assignment.type.incompatible)
        sl = mB.longValue();
        // :: error: (assignment.type.incompatible)
        sf = mB.floatValue();
        // :: error: (assignment.type.incompatible)
        sd = mB.doubleValue();

        System.out.println(mB.toString());
        System.out.println(Byte.toString(mb));
        System.out.println(mB.hashCode());
        System.out.println(Byte.hashCode(mb));

        mB.equals(mB);
        // :: error: (comparison.unit.mismatch)
        mB.equals(sB);

        mB.compareTo(mB);
        // :: error: (comparison.unit.mismatch)
        mB.compareTo(sB);

        Byte.compare(mb, mb);
        // :: error: (comparison.unit.mismatch)
        Byte.compare(mb, sb);

        mI = Byte.toUnsignedInt(mb);
        mL = Byte.toUnsignedLong(mb);
    }

    void testShort() {
        mS = Short.valueOf(ms);
        // mS = new Short(ms);

        mb = mS.byteValue();
        ms = mS.shortValue();
        mi = mS.intValue();
        ml = mS.longValue();
        mf = mS.floatValue();
        md = mS.doubleValue();

        // :: error: (assignment.type.incompatible)
        sS = Short.valueOf(ms);
        // :: error: (assignment.type.incompatible)
        sb = mS.byteValue();
        // :: error: (assignment.type.incompatible)
        ss = mS.shortValue();
        // :: error: (assignment.type.incompatible)
        si = mS.intValue();
        // :: error: (assignment.type.incompatible)
        sl = mS.longValue();
        // :: error: (assignment.type.incompatible)
        sf = mS.floatValue();
        // :: error: (assignment.type.incompatible)
        sd = mS.doubleValue();

        System.out.println(mS.toString());
        System.out.println(Short.toString(ms));
        System.out.println(mS.hashCode());
        System.out.println(Short.hashCode(ms));

        mS.equals(mS);
        // :: error: (comparison.unit.mismatch)
        mS.equals(sS);

        mS.compareTo(mS);
        // :: error: (comparison.unit.mismatch)
        mS.compareTo(sS);

        Short.compare(ms, ms);
        // :: error: (comparison.unit.mismatch)
        Short.compare(ms, ss);

        ms = Short.reverseBytes(ms);
        mI = Short.toUnsignedInt(ms);
        mL = Short.toUnsignedLong(ms);
    }

    void testInteger() {
        // autobox
        mI = mi;
        // autounbox
        mi = mI;

        mI = Integer.valueOf(mi);
        // mI = new Integer(mi);

        mb = mI.byteValue();
        ms = mI.shortValue();
        mi = mI.intValue();
        ml = mI.longValue();
        mf = mI.floatValue();
        md = mI.doubleValue();

        // :: error: (assignment.type.incompatible)
        sI = Integer.valueOf(mi);
        // :: error: (assignment.type.incompatible)
        sb = mI.byteValue();
        // :: error: (assignment.type.incompatible)
        ss = mI.shortValue();
        // :: error: (assignment.type.incompatible)
        si = mI.intValue();
        // :: error: (assignment.type.incompatible)
        sl = mI.longValue();
        // :: error: (assignment.type.incompatible)
        sf = mI.floatValue();
        // :: error: (assignment.type.incompatible)
        sd = mI.doubleValue();

        System.out.println(mI.toString());
        System.out.println(Integer.toString(mi));
        System.out.println(Integer.toString(mi, 30));
        System.out.println(Integer.toUnsignedString(mi));
        System.out.println(Integer.toUnsignedString(mi, 40));
        System.out.println(Integer.toHexString(mi));
        System.out.println(Integer.toOctalString(mi));
        System.out.println(Integer.toBinaryString(mi));
        System.out.println(mI.hashCode());
        System.out.println(Integer.hashCode(mi));

        mI = Integer.getInteger("10", mi);
        // :: error: (assignment.type.incompatible)
        sI = Integer.getInteger("10", mi);

        mI = Integer.getInteger("10", mI);
        // :: error: (assignment.type.incompatible)
        sI = Integer.getInteger("10", mI);

        mI.equals(mI);
        // :: error: (comparison.unit.mismatch)
        mI.equals(sI);

        mI.compareTo(mI);
        // :: error: (comparison.unit.mismatch)
        mI.compareTo(sI);

        Integer.compare(mi, mi);
        // :: error: (comparison.unit.mismatch)
        Integer.compare(mi, si);

        Integer.compareUnsigned(mi, mi);
        // :: error: (comparison.unit.mismatch)
        Integer.compareUnsigned(mi, si);

        mi = Integer.sum(mi, mi);
        // :: error: (assignment.type.incompatible)
        mi = Integer.sum(mi, si);

        @Dimensionless int a = Integer.divideUnsigned(mi, mi);
        // :: error: (assignment.type.incompatible)
        mi = Integer.divideUnsigned(mi, mi);

        mi = Integer.remainderUnsigned(mi, si);
        // :: error: (assignment.type.incompatible)
        si = Integer.remainderUnsigned(mi, mi);

        mi = Integer.highestOneBit(mi);
        mi = Integer.lowestOneBit(mi);
        @Dimensionless int x = Integer.numberOfLeadingZeros(mi);
        x = Integer.numberOfTrailingZeros(mi);
        x = Integer.bitCount(mi);
        x = Integer.signum(mi);

        mi = Integer.rotateLeft(mi, 10);
        mi = Integer.rotateRight(mi, 20);
        mi = Integer.reverse(mi);
        mi = Integer.reverseBytes(mi);
        mL = Integer.toUnsignedLong(mi);

        mi = Integer.max(mi, mi);
        // :: error: (assignment.type.incompatible)
        mi = Integer.max(mi, si);

        mi = Integer.min(mi, mi);
        // :: error: (assignment.type.incompatible)
        mi = Integer.min(mi, si);
    }

    void testLong() {
        // autobox
        mL = ml;
        // autounbox
        ml = mL;

        mL = Long.valueOf(ml);
        // mL = new Long(ml);

        mb = mL.byteValue();
        ms = mL.shortValue();
        mi = mL.intValue();
        ml = mL.longValue();
        mf = mL.floatValue();
        md = mL.doubleValue();

        // :: error: (assignment.type.incompatible)
        sL = Long.valueOf(ml);
        // :: error: (assignment.type.incompatible)
        sb = mL.byteValue();
        // :: error: (assignment.type.incompatible)
        ss = mL.shortValue();
        // :: error: (assignment.type.incompatible)
        si = mL.intValue();
        // :: error: (assignment.type.incompatible)
        sl = mL.longValue();
        // :: error: (assignment.type.incompatible)
        sf = mL.floatValue();
        // :: error: (assignment.type.incompatible)
        sd = mL.doubleValue();

        System.out.println(mL.toString());
        System.out.println(Long.toString(ml));
        System.out.println(Long.toString(ml, 30));
        System.out.println(Long.toUnsignedString(ml));
        System.out.println(Long.toUnsignedString(ml, 40));
        System.out.println(Long.toHexString(ml));
        System.out.println(Long.toOctalString(ml));
        System.out.println(Long.toBinaryString(ml));
        System.out.println(mL.hashCode());
        System.out.println(Long.hashCode(ml));

        mL = Long.getLong("10", ml);
        // :: error: (assignment.type.incompatible)
        sL = Long.getLong("10", ml);

        mL = Long.getLong("10", mL);
        // :: error: (assignment.type.incompatible)
        sL = Long.getLong("10", mL);

        mL.equals(mL);
        // :: error: (comparison.unit.mismatch)
        mL.equals(sL);

        mL.compareTo(mL);
        // :: error: (comparison.unit.mismatch)
        mL.compareTo(sL);

        Long.compare(ml, ml);
        // :: error: (comparison.unit.mismatch)
        Long.compare(ml, sl);

        Long.compareUnsigned(ml, ml);
        // :: error: (comparison.unit.mismatch)
        Long.compareUnsigned(ml, sl);

        ml = Long.sum(ml, ml);
        // :: error: (assignment.type.incompatible)
        ml = Long.sum(ml, sl);
        @Dimensionless long a = Long.divideUnsigned(ml, ml);
        // :: error: (assignment.type.incompatible)
        ml = Long.divideUnsigned(ml, ml);

        ml = Long.remainderUnsigned(ml, sl);
        // :: error: (assignment.type.incompatible)
        sl = Long.remainderUnsigned(ml, ml);

        ml = Long.highestOneBit(ml);
        ml = Long.lowestOneBit(ml);
        @Dimensionless int x = Long.numberOfLeadingZeros(ml);
        x = Long.numberOfTrailingZeros(ml);
        x = Long.bitCount(ml);
        x = Long.signum(ml);

        ml = Long.rotateLeft(ml, 10);
        ml = Long.rotateRight(ml, 20);
        ml = Long.reverse(ml);
        ml = Long.reverseBytes(ml);

        ml = Long.max(ml, ml);
        // :: error: (assignment.type.incompatible)
        ml = Long.max(ml, sl);

        ml = Long.min(ml, ml);
        // :: error: (assignment.type.incompatible)
        ml = Long.min(ml, sl);
    }

    void testFloat() {
        // autobox
        mF = mf;
        // autounbox
        mf = mF;

        mF = Float.valueOf(mf);
        // mF = new Float(mf);
        // mF = new Float(md);

        mb = mF.byteValue();
        ms = mF.shortValue();
        mi = mF.intValue();
        ml = mF.longValue();
        mf = mF.floatValue();
        md = mF.doubleValue();

        // :: error: (assignment.type.incompatible)
        sF = Float.valueOf(mf);
        // :: error: (assignment.type.incompatible)
        sb = mF.byteValue();
        // :: error: (assignment.type.incompatible)
        ss = mF.shortValue();
        // :: error: (assignment.type.incompatible)
        si = mF.intValue();
        // :: error: (assignment.type.incompatible)
        sl = mF.longValue();
        // :: error: (assignment.type.incompatible)
        sf = mF.floatValue();
        // :: error: (assignment.type.incompatible)
        sd = mF.doubleValue();

        System.out.println(mF.toString());
        System.out.println(Float.toString(mf));
        System.out.println(Float.toHexString(mf));
        System.out.println(mF.hashCode());
        System.out.println(Float.hashCode(mf));

        mF.isNaN();
        Float.isNaN(mf);
        mF.isInfinite();
        Float.isInfinite(mf);
        Float.isFinite(mf);

        mF.equals(mF);
        // :: error: (comparison.unit.mismatch)
        mF.equals(sF);

        mF.compareTo(mF);
        // :: error: (comparison.unit.mismatch)
        mF.compareTo(sF);

        Float.compare(mf, mf);
        // :: error: (comparison.unit.mismatch)
        Float.compare(mf, sf);

        mf = Float.sum(mf, mf);
        // :: error: (assignment.type.incompatible)
        mf = Float.sum(mf, sf);

        mi = Float.floatToIntBits(mf);
        mi = Float.floatToRawIntBits(mf);
        mf = Float.intBitsToFloat(mi);

        mf = Float.max(mf, mf);
        // :: error: (assignment.type.incompatible)
        mf = Float.max(mf, sf);

        mf = Float.min(mf, mf);
        // :: error: (assignment.type.incompatible)
        mf = Float.min(mf, sf);
    }

    void testDouble() {
        // autobox
        mD = md;
        // autounbox
        md = mD;

        mD = Double.valueOf(md);
        // mD = new Double(md);

        mb = mD.byteValue();
        ms = mD.shortValue();
        mi = mD.intValue();
        ml = mD.longValue();
        mf = mD.floatValue();
        md = mD.doubleValue();

        // :: error: (assignment.type.incompatible)
        sD = Double.valueOf(md);
        // :: error: (assignment.type.incompatible)
        sb = mD.byteValue();
        // :: error: (assignment.type.incompatible)
        ss = mD.shortValue();
        // :: error: (assignment.type.incompatible)
        si = mD.intValue();
        // :: error: (assignment.type.incompatible)
        sl = mD.longValue();
        // :: error: (assignment.type.incompatible)
        sf = mD.floatValue();
        // :: error: (assignment.type.incompatible)
        sd = mD.doubleValue();

        System.out.println(mD.toString());
        System.out.println(Double.toString(md));
        System.out.println(Double.toHexString(md));
        System.out.println(mD.hashCode());
        System.out.println(Double.hashCode(md));

        mD.isNaN();
        Double.isNaN(md);
        mD.isInfinite();
        Double.isInfinite(md);
        Double.isFinite(md);

        mD.equals(mD);
        // :: error: (comparison.unit.mismatch)
        mD.equals(sD);

        mD.compareTo(mD);
        // :: error: (comparison.unit.mismatch)
        mD.compareTo(sD);

        Double.compare(md, md);
        // :: error: (comparison.unit.mismatch)
        Double.compare(md, sd);

        md = Double.sum(md, md);
        // :: error: (assignment.type.incompatible)
        md = Double.sum(md, sd);

        ml = Double.doubleToLongBits(md);
        ml = Double.doubleToRawLongBits(md);
        md = Double.longBitsToDouble(ml);

        md = Double.max(md, md);
        // :: error: (assignment.type.incompatible)
        md = Double.max(md, sd);

        md = Double.min(md, md);
        // :: error: (assignment.type.incompatible)
        md = Double.min(md, sd);
    }
}
