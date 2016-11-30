package ss.week3.pw;

public class TimedPassword extends Password {

	private long validTime;
	private long expirationTime;
	
	public TimedPassword(long theValidTime) {
		validTime = theValidTime;
		expirationTime = theValidTime + System.currentTimeMillis();
	}
	
	public TimedPassword() {
		validTime = 1000 * 60 * 60 * 24 * 365;
		expirationTime = validTime + System.currentTimeMillis();
	}
	
	public boolean isExpired() {
		return System.currentTimeMillis() >= expirationTime;
	}
	
	public boolean setWord(String oldpass, String newpass) {
		expirationTime = validTime + System.currentTimeMillis();
		return super.setWord(oldpass, newpass);
	}
}
