package ss.week1;

public class DollarsAndCentsCounter {

	private int cdollars;
	private int ccents;

	public DollarsAndCentsCounter() {
		cdollars = 0;
		ccents = 0;
	}

	// The dollar count.
	public int dollars() {
		return this.cdollars;
	}

	// The cents count
	public int cents() {
		return this.ccents;
	}

	// Add the specified dollars and cents to this counter.
	public void add(int dollars, int cents) {
		this.ccents = (this.ccents + cents) % 100;
		this.cdollars += dollars + (this.ccents + cents) / 100;
	}

	// Reset this counter to 0
	public void reset() {
		this.cdollars = 0;
		this.ccents = 0;
	}

}
