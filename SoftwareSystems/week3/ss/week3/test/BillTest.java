package ss.week3.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ss.week3.hotel.Bill;
import ss.week3.hotel.TestItem;

public class BillTest {
	private Bill printBill;
	private Bill.Item item1;
	private Bill.Item item2;
	
	@Before
	public void setUp() {
		printBill = new Bill(System.out);	
		item1 = new TestItem("één", 1.00);
		item2 = new TestItem("twee", 200.00);
	}

	@Test
	public final void testBill() {
		assertTrue(printBill.getSum() == 0.00);
		assertTrue(item1.getAmount() == 1.00);
		assertTrue(item2.getAmount() == 200.00);
	}

	@Test
	public final void testNewItem() {
		printBill.newItem(item1);
		assertTrue(printBill.getSum() == 1.00);
	}

	@Test
	public final void testClose() {
		printBill.newItem(item1);
		printBill.newItem(item2);
		printBill.close();
	}

	@Test
	public final void testGetSum() {
		printBill.newItem(item1);
		printBill.newItem(item2);
		assertTrue(printBill.getSum() == 201.00);
	}

}
