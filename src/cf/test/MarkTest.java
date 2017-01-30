package cf.test;

import static org.junit.Assert.*;

import org.junit.Test;

import cf.model.Mark;

public class MarkTest {

	@Test
	public final void testOther() {
		assertEquals(Mark.XX.other(), Mark.OO);
		assertEquals(Mark.OO.other(), Mark.XX);
		assertEquals(Mark.EMPTY.other(), Mark.EMPTY);
	}

	@Test
	public final void testToString() {
		assertEquals(Mark.XX.toString(), "X");
		assertEquals(Mark.OO.toString(), "O");
		assertEquals(Mark.EMPTY.toString(), " ");
	}

	@Test
	public final void testIsEmpty() {
		assertTrue(Mark.EMPTY.isEmpty());
		assertFalse(Mark.XX.isEmpty());
		assertFalse(Mark.OO.isEmpty());
	}

}
