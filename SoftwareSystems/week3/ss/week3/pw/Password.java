package ss.week3.pw;

public class Password {

	//Instance Variables
	
	private String curpass;
	private Checker checker;
	private String factoryPassword;
	
	//Constructor
	
	public Password(Checker thisChecker) {
		checker = thisChecker;
		factoryPassword = checker.generatePassword();
		curpass = factoryPassword;
	}
	
	public Password() {
		this(new BasicChecker());
	}
	
	//Commands
	
	public boolean acceptable(String suggestion) {
		return checker.acceptable(suggestion);
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
	
	//Queries
	public Checker getChecker() {
		return checker;
	}
	
	public String getFactoryPassword() {
		return factoryPassword;
	}
}
