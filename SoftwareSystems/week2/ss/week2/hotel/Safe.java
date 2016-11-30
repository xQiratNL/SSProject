package ss.week2.hotel;

public class Safe {

	//-----------Instance variables----------
	//@ private invariant ( open==true ) ==> ( active==true );
	
	private boolean active;
	private boolean open;
	private Password password;
	
	//-----------Constructor-------------
	
	//@ ensures isActive() == false;
	//@ ensures isOpen() == false;
	//@ ensures getPassword().testWord(Password.INITIAL) == true;
	public Safe() {
		active = false;
		open = false;
		password = new Password();
	}
	
	//----------Commands-----------------
	//Receives password, if password is correct, activates safe.
	//@ ensures isActive() == true;
	public void activate(String thePassword) {
		active = password.testWord(thePassword);
	}
	
	//Closes and deactivates safe.
	//@ ensures isOpen() == false;
	//@ ensures isActive() == false;
	public void deactivate() {
		open = false;
		active = false;
	}
	
	//Receives password, if password is correct, opens safe.
	//@ requires isActive() == true;
	//@ ensures isOpen() == true;
	//@ ensures isActive() == \old(isActive());
	public void open(String thePassword) {
		assert active == true;
		open = password.testWord(thePassword);
	}
	
	//Closes safe
	//@ ensures isOpen() == false;
	//@ ensures isActive() == \old(isActive());
	public void close() {
		open = false;
	}
	
	//------------Queries---------------
	// returns active state
	//@ ensures isActive() == \old(isActive());
	//@ ensures isOpen() == \old(isOpen());
	/*@ pure */ public boolean isActive() {
		return active;
	}
	
	//returns open state
	//@ ensures isActive() == \old(isActive());
	//@ ensures isOpen() == \old(isOpen());
	/*@ pure */ public boolean isOpen() {
		return open;
	}
	
	// returns password object
	//@ ensures isActive() == \old(isActive());
	//@ ensures isOpen() == \old(isOpen());
	/*@ pure */ public Password getPassword() {
		return password;
	}
	
	//---------------Main---------------
	
	public static void main(String[] args) {
		Safe safe = new Safe();
		safe.open("testtest");
	}
	
}
