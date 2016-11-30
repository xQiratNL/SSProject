package ss.week3.pw;

public interface Checker {

	/**
	 * Returns true if the parameter is an acceptable password.
	 * Returns false otherwise.
	 */
	public boolean acceptable(String thePassword);
	
	/**
	 * Returns password which is acceptable.
	 */
	public String generatePassword();
}
