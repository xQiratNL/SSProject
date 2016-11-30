package ss.week1;

public class Employee {

	public static void main(String[] args) {
		System.out.println((new Employee()).pay());

	}

	private int hours;
	private double rate;

	public Employee() {
		hours = 50;
		rate = 10;
	}

	public double pay() {
		if (hours <= 40) {
			return hours * rate;
		} else {
			return 40 * rate + (hours - 40) * 1.5 * rate;
		}
	}

}
