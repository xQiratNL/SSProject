package cf.game;

public enum Mark {

	EMPTY, XX, OO;

    /*@
       ensures this == Mark.XX ==> \result == Mark.OO;
       ensures this == Mark.OO ==> \result == Mark.XX;
       ensures this == Mark.EMPTY ==> \result == Mark.EMPTY;
     */
    /**
     * Returns the other mark.
     * 
     * @return the other mark is this mark is not EMPTY or EMPTY
     */
    public Mark other() {
        if (this == XX) {
            return OO;
        } else if (this == OO) {
            return XX;
        } else {
            return EMPTY;
        }
    }
    
    /**
     * @return string (length 1) representation of a mark.
     */
    public String toString() {
    	if (this == XX) {
    		return "X";
    	} else if (this == OO) {
    		return "O";
    	} else {
    		return " ";
    	}
    }
    
    /**
     * Returns true if mark is the empty mark.
     * @return true if mark is empty.
     */
    public boolean isEmpty() {
    	return this.equals(EMPTY);
    }
}
