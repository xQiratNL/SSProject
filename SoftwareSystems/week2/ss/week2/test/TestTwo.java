package ss.week2.test;

import ss.week2.ThreeWayLampTwo;

public class TestTwo {
	public static void main(String[] argv) {
		ThreeWayLampTestTwo test = new ThreeWayLampTestTwo();
		test.runTest();
	}
}

class ThreeWayLampTestTwo {
	
	// Instance variable
	private ThreeWayLampTwo lamp;
	
	// Constructor
	public ThreeWayLampTestTwo() {
		lamp = new ThreeWayLampTwo();
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
