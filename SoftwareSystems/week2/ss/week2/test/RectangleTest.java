package ss.week2.test;

import org.junit.Before;
import org.junit.Test;
import ss.week2.Rectangle;

import static org.junit.Assert.assertEquals;

public class RectangleTest {
	private Rectangle rectangle;
	
	@Before
	public void setUp() {
		rectangle = new Rectangle(5, 10);
	}
	
	@Test
	public void testInitialcondition() {
		assertEquals(5, rectangle.length());
		assertEquals(10, rectangle.width());
	}
	
	@Test
	public void testArea() {
		assertEquals(50, rectangle.area());
	}
	
	@Test
	public void testPerimeter() {
		assertEquals(30, rectangle.perimeter());
	}
	
}
