package ss.week3.pw;

public class StrongChecker extends BasicChecker implements Checker {
	
	public static final String INITPASS = "initial1";
	
	@Override
	public boolean acceptable(String thePassword) {
		return super.acceptable(thePassword) && Character.isLetter(thePassword.charAt(0)) 
				&& Character.isDigit(thePassword.charAt(thePassword.length() - 1));
	}
	
	@Override
	public String generatePassword() {
		return INITPASS;
	}
}
