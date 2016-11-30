package ss.week3.hotel;

public class Password {

	//Instance Variables
	
	public static final String INITIAL = "initialpassword";
	private String curpass;
	
	//Constructor
	
	public Password() {
		curpass = INITIAL;
	}
	
	//Commands
	
	public boolean acceptable(String suggestion) {
		if (suggestion.length() < 6 || suggestion.contains(" ")) {
			return false;
		} else {
			return true;
		}
	}
	
	/*@ pure */ public boolean testWord(String test) {
		if (curpass.equals(test)) {
			return true;
		} else {
			return false;
		}
	}
	
	public boolean setWord(String oldpass, String newpass) {
		if (curpass.equals(oldpass) && acceptable(newpass)) {
			curpass = newpass;
			return true;
		} else {
			return false;
		}
	}
}
