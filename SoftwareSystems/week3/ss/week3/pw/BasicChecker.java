package ss.week3.pw;

public class BasicChecker implements Checker {

	public static final String INITPASS = "initial";
	
	@Override
	public boolean acceptable(String thePassword) {
		return thePassword.length() >= 6 && !thePassword.contains(" ");
	}
	
	@Override
	public String generatePassword() {
		return INITPASS;
	}
	

}
