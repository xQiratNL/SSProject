package connectfour;

public class Mark {
	
	private String string;
	private boolean empty;
	
	public Mark() {
		string = "   ";
		empty = true;
	}
	
	public Mark (String mark) {
		string = mark;
		empty = false;
	}
    
    public String toString() {
    	return string;
    }
    
    public boolean isEmpty() {
    	return empty;
    }
}
