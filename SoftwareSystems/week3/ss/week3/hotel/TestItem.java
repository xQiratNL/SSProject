package ss.week3.hotel;

public class TestItem implements Bill.Item {

	//Instance variables
	private String text;
	private double amount;
	
	public TestItem(String theText, Double theAmount) {
		text = theText;
		amount = theAmount;
	}
	
	@Override
	public double getAmount() {
		return amount;
	}
	
	@Override
	public String toString() {
		return String.format("%-10s %10.2f", text, amount);
	}

}
