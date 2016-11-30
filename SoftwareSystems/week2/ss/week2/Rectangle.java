package ss.week2;

public class Rectangle {
    private int length;
    private int width;
    
    //@ private invariant length >= 0;
    //@ private invariant width >= 0;

    /**
     * Create a new Rectangle with the specified length and width.
     */
    //@ requires theLength >= 0;
    //@ requires theWidth >= 0;
    public Rectangle(int theLength, int theWidth) {
    	assert theLength >= 0;
    	assert theWidth >= 0;
    	length = theLength;
    	width = theWidth;
    }
 
    /**
     * The length of this Rectangle.
     */
    
    //@ ensures \result >= 0;
    /*@ pure */ public int length() {
    	assert this.length >= 0;
    	return this.length;
    }

    /**
     * The width of this Rectangle.
     */
    
    //@ ensures \result >= 0;
    /*@ pure */ public int width() {
    	assert this.width >= 0;
    	return this.width;
    }

    /**
     * The area of this Rectangle.
     */ 
    //@ ensures \result == length() * width();
    public int area() {
    	assert this.width >= 0;
    	assert this.length >= 0;    	
    	return this.length * this.width;
    }

    /**
     * The perimeter of this Rectangle.
     */
    
    //@ ensures \result == 2 * length() + 2 * width();
    public int perimeter() {
    	assert this.width >= 0;
    	assert this.length >= 0;
    	return 2 * this.width + 2 * this.length;
    }
}
