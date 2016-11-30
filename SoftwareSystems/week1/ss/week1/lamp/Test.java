package ss.week1.lamp;

public class Test {
	public static void main(String[] argv) {
		ThreeWayLampTest test = new ThreeWayLampTest();
		test.runTest();
	}
}

class ThreeWayLampTest {
	
	// Instance variable
	private ThreeWayLamp lamp;
	
	// Constructor
	public ThreeWayLampTest() {
		lamp = new ThreeWayLamp();
	}
	
	//Commands
	public void runTest() {
		testInitialSetting();
		testSwitchSetting();
	}
	
	private void testInitialSetting() {
		System.out.println("testInitialSetting:");
		System.out.println("Initial Setting: " + lamp.getSetting());
	}

	private void testSwitchSetting() {
		System.out.println("testSwitchSetting:");
		lamp.switchSetting();
		System.out.println("After 1 change " + lamp.getSetting());
		lamp.switchSetting();
		System.out.println("After 2 changes " + lamp.getSetting());
		lamp.switchSetting();
		System.out.println("After 3 changes " + lamp.getSetting());
		lamp.switchSetting();
		System.out.println("After 4 changes " + lamp.getSetting());
	}
}
