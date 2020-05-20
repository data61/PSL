    interface Counter {

        public int incr();

        public int reset();
    }

class CounterImpl implements Counter {
    protected int value;

    public int incr() 
    {
        int dummy;
        res = this.value;
        res = (int) res + 1;
        this.value = res;
    }

    public int reset() 
    {
        int dummy;
        this.value=0;
        res = (int) 0;
    }
}

class UndoCounter extends CounterImpl {
    private int save;

    public int incr()
    {
        int dummy;
        res = this.value;
        this.save = res;
        res = res + 1;
        this.value = res;
    }

    public int un_do()
    {
        int res2;
        res = this.save;
        res2 = this.value;
        this.value = res;
        this.save  = res2;
    }
}
