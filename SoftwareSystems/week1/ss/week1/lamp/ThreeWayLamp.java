package ss.week1.lamp;

public class ThreeWayLamp {
	public static final int OUT = 0;
	public static final int LOW = 1;
	public static final int MEDIUM = 2;
	public static final int HIGH = 3;

	private int setting;
	
	public ThreeWayLamp() {
		setting = OUT;
	}

	public int getSetting() {
		return setting;
	}

	public void switchSetting() {
		setting = (setting + 1) % 4;
	}
}
