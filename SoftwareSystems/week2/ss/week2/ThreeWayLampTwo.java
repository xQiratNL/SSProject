package ss.week2;

public class ThreeWayLampTwo {
	
	private enum Setting { OUT, LOW, MEDIUM, HIGH };

	private Setting setting;
	
	//@ ensures getSetting() == Setting.OUT;
	public ThreeWayLampTwo() {
		setting = Setting.OUT;
	}

	/*@ pure */ public Setting getSetting() {
		return setting;
	}
	
	//@ ensures \old(getSetting()) == Setting.OUT ==> getSetting() == Setting.LOW;
	//@ ensures \old(getSetting()) == Setting.LOW ==> getSetting() == Setting.MEDIUM;
	//@ ensures \old(getSetting()) == Setting.MEDIUM ==> getSetting() == Setting.HIGH;
	//@ ensures \old(getSetting()) == Setting.HIGH ==> getSetting() == Setting.OUT;
	public void switchSetting() {
		switch (setting) {
			case OUT:
				setting = Setting.LOW;
				break;
			case LOW:
				setting = Setting.MEDIUM;
				break;
			case MEDIUM:
				setting = Setting.HIGH;
				break;
			case HIGH:
				setting = Setting.OUT;
		}
			
	}
}
