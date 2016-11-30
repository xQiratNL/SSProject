package ss.week2.test;

import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;

import ss.week2.hotel.Safe;
import ss.week2.hotel.Password;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SafeTest {
	private Safe safe;
	private Safe openSafe;
	private Safe activeSafe;
	private String wrongPass;
	
	@Before
	public void setUp() {
		safe = new Safe();
		
		openSafe = new Safe();
		openSafe.activate(Password.INITIAL);
		openSafe.open(Password.INITIAL);
		
		activeSafe = new Safe();
		activeSafe.activate(Password.INITIAL);
	}

	@Test
	public final void testSetUp() {
		assertFalse(safe.isActive());
		assertFalse(safe.isOpen());
		assertTrue(safe.getPassword().testWord(Password.INITIAL));
		assertFalse(safe.getPassword().testWord(wrongPass));
		
		assertTrue(openSafe.isActive());
		assertTrue(openSafe.isOpen());
		assertFalse(openSafe.getPassword().testWord(wrongPass));
		
		assertTrue(activeSafe.isActive());
		assertFalse(activeSafe.isOpen());
		assertFalse(activeSafe.getPassword().testWord(wrongPass));
	}

	@Test
	public final void testActivateCorrectPassword() {
		safe.activate(Password.INITIAL);
		assertTrue(safe.isActive());
		assertFalse(safe.isOpen());
	}
	
	@Test
	public final void testActivateWrongPassword() {
		safe.activate(wrongPass);
		assertFalse(safe.isActive());
		assertFalse(safe.isOpen());
	}

	@Test
	public final void testDeactivate() {
		openSafe.deactivate();
		assertFalse(openSafe.isOpen());
		assertFalse(openSafe.isActive());
	}

	@Test
	public final void testOpenCorrectPassword() {
		activeSafe.open(Password.INITIAL);
		assertTrue(activeSafe.isOpen());
		assertTrue(activeSafe.isActive());
	}
	
	@Test
	public final void testOpenWrongPassword() {
		activeSafe.open(wrongPass);
		assertFalse(activeSafe.isOpen());
		assertTrue(activeSafe.isActive());
	}

	@Test
	public final void testClose() {
		openSafe.close();
		assertFalse(openSafe.isOpen());
		assertTrue(openSafe.isActive());
	}

}
