package ss.week2;

public class ThreeWayLamp {
	public static final int OUT = 0;
	public static final int LOW = 1;
	public static final int MEDIUM = 2;
	public static final int HIGH = 3;

	private int setting;
	//@ private invariant setting == OUT || setting == LOW || setting == MEDIUM || setting == HIGH;
	
	
	//@ ensures getSetting() == 0;
	public ThreeWayLamp() {
		setting = OUT;
	}

	/*@ pure */ public int getSetting() {
		assert setting == OUT || setting == LOW || setting == MEDIUM || setting == HIGH;
		return setting;
	}
	
	//@ ensures \old(getSetting()) == OUT ==> getSetting() == LOW;
	//@ ensures \old(getSetting()) == LOW ==> getSetting() == MEDIUM;
	//@ ensures \old(getSetting()) == MEDIUM ==> getSetting() == HIGH;
	//@ ensures \old(getSetting()) == HIGH ==> getSetting() == OUT;
	public void switchSetting() {
		assert setting == OUT || setting == LOW || setting == MEDIUM || setting == HIGH;
		setting = (setting + 1) % 4;
	}
}
