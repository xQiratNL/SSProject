package ss.week3.hotel;

public class Bill {	
	//Nested interfaces
	
	public static interface Item {
		/**
		 * Returns the amount.
		 */
		public double getAmount();
	}
	
	//Instance variables
	private java.io.PrintStream outStream;
	private double sum;
	
	//Constructors
	public Bill(java.io.PrintStream theOutStream) {
		outStream = theOutStream;
	}
	
	//Commands
	public void newItem(Bill.Item item) {
		sum += item.getAmount();
		if (outStream != null) {
			outStream.println(item.toString());
		}
	}
	
	public void close() {
		if (outStream != null) {
			outStream.println(String.format("%-10s %10.2f", "", getSum()));
		}
	}
	
	//Queries
	public double getSum() {
		return sum;
	}
	
}
