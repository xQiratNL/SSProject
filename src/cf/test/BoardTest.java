package cf.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import cf.model.*;

public class BoardTest {

	private int[] fields;
	private Board board;
	@Before
	public void setUp() throws Exception {
		board = new Board(3);
		fields = new int[3*3*3];
		for (int i = 0; i < fields.length; i++) {
			fields[i] = i;
		}
	}

	@Test
	public final void testBoard() {
		for (int i: fields) {
			assertEquals(board.getField(i), Mark.EMPTY);
		}
		assertEquals(board.getDim(), 3);
		assertEquals(board.getSize(), 3 * 3 * 3);
	}

	@Test
	public final void testReset() {
		for (int i: fields) {
			assertEquals(board.getField(i), Mark.EMPTY);
		}
	}

	@Test
	public final void testDeepCopy() {
		Board bCopy = board.deepCopy();
		for (int i: fields) {
			assertEquals(board.getField(i), bCopy.getField(i));
		}
		assertEquals(board.getDim(), bCopy.getDim());
		assertEquals(board.getSize(), bCopy.getSize());
		bCopy.setField(10, Mark.XX);
		assertEquals(board.getField(10), Mark.EMPTY);
	}

	@Test
	public final void testIndex() {
		assertEquals(board.index(0, 0, 0), 0);
		assertEquals(board.index(0, 0, 1), 9);
	}

	@Test
	public final void testCoordinates() {
		for (int i: fields) {
			assertEquals(i, board.index(board.coordinates(i)[0], board.coordinates(i)[1], board.coordinates(i)[2]));
		}
	}

	@Test
	public final void testIsFieldIntIntInt() {
		assertTrue(board.isField(0,0,0));
		assertTrue(board.isField(2,2,2));
		assertFalse(board.isField(3,3,3));
	}

	@Test
	public final void testIsFieldInt() {
		assertTrue(board.isField(0));
		assertTrue(board.isField(26));
		assertFalse(board.isField(27));
	}

	@Test
	public final void testGetFieldIntIntInt() {
		board.setField(1, 1, 1, Mark.XX);
		assertEquals(Mark.XX, board.getField(1, 1, 1));
	}

	@Test
	public final void testGetFieldInt() {
		board.setField(3, Mark.XX);
		assertEquals(Mark.XX, board.getField(3));
	}

	@Test
	public final void testIsEmptyFieldIntIntInt() {
		assertTrue(board.isEmptyField(2,2,2));
		board.setField(2, 2, 2, Mark.XX);
		assertFalse(board.isEmptyField(2,2,2));
	}

	@Test
	public final void testIsEmptyFieldInt() {
		assertTrue(board.isEmptyField(2));
		board.setField(2, Mark.XX);
		assertFalse(board.isEmptyField(2));
	}

	@Test
	public final void testIsValidMove() {
		assertTrue(board.isValidMove(0,2,0));
		board.setField(0,2,0, Mark.XX);
		assertFalse(board.isValidMove(0,2,0));
		assertFalse(board.isValidMove(2,2,2));
		assertFalse(board.isValidMove(10, 10, 10));
	}

	@Test
	public final void testIsFull() {
		assertFalse(board.isFull());
		for (int i: fields) {
			assertFalse(board.isFull());
			board.setField(i, Mark.XX);
		}
		assertTrue(board.isFull());
	}

	@Test
	public final void testSetFieldIntIntIntMark() {
		assertEquals(board.getField(2,2,2), Mark.EMPTY);
		board.setField(2, 2, 2, Mark.XX);
		assertEquals(board.getField(2,2,2), Mark.XX);
	}

	@Test
	public final void testSetFieldIntMark() {
		assertEquals(board.getField(2), Mark.EMPTY);
		board.setField(2, Mark.XX);
		assertEquals(board.getField(2), Mark.XX);
	}

	@Test
	public final void testIsWinner() {
		assertFalse(board.isWinner(Mark.XX));
		assertFalse(board.isWinner(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0, mark);
		board.setField(1, mark);
		board.setField(2, mark);
		assertTrue(board.isWinner(Mark.XX));
		assertFalse(board.isWinner(Mark.OO));
	}

	@Test
	public final void testHasRow() {
		assertFalse(board.hasRow(Mark.XX));
		assertFalse(board.hasRow(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0, mark);
		board.setField(1, mark);
		board.setField(2, mark);
		assertTrue(board.hasRow(Mark.XX));
		assertFalse(board.hasRow(Mark.OO));
	}

	@Test
	public final void testHasColumn() {
		assertFalse(board.hasColumn(Mark.XX));
		assertFalse(board.hasColumn(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0, mark);
		board.setField(3, mark);
		board.setField(6, mark);
		assertTrue(board.hasColumn(Mark.XX));
		assertFalse(board.hasColumn(Mark.OO));
	}

	@Test
	public final void testHasBar() {
		assertFalse(board.hasBar(Mark.XX));
		assertFalse(board.hasBar(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0, mark);
		board.setField(9, mark);
		board.setField(18, mark);
		assertTrue(board.hasBar(Mark.XX));
		assertFalse(board.hasBar(Mark.OO));
	}

	@Test
	public final void testHasZDiagonal() {
		assertFalse(board.hasZDiagonal(Mark.XX));
		assertFalse(board.hasZDiagonal(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0, mark);
		board.setField(4, mark);
		board.setField(8, mark);
		assertTrue(board.hasZDiagonal(Mark.XX));
		assertFalse(board.hasZDiagonal(Mark.OO));
	}

	@Test
	public final void testHasYDiagonal() {
		assertFalse(board.hasYDiagonal(Mark.XX));
		assertFalse(board.hasYDiagonal(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0,0,0, mark);
		board.setField(1,0,1, mark);
		board.setField(2,0,2, mark);
		assertTrue(board.hasYDiagonal(Mark.XX));
		assertFalse(board.hasYDiagonal(Mark.OO));
	}

	@Test
	public final void testHasXDiagonal() {
		assertFalse(board.hasXDiagonal(Mark.XX));
		assertFalse(board.hasXDiagonal(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0,0,0, mark);
		board.setField(0,1,1, mark);
		board.setField(0,2,2, mark);
		assertTrue(board.hasXDiagonal(Mark.XX));
		assertFalse(board.hasXDiagonal(Mark.OO));
	}

	@Test
	public final void testHasCrossDiagonal() {
		assertFalse(board.hasCrossDiagonal(Mark.XX));
		assertFalse(board.hasCrossDiagonal(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0,0,0, mark);
		board.setField(1,1,1, mark);
		board.setField(2,2,2, mark);
		assertTrue(board.hasCrossDiagonal(Mark.XX));
		assertFalse(board.hasCrossDiagonal(Mark.OO));
	}

	@Test
	public final void testHasWinner() {
		assertFalse(board.hasCrossDiagonal(Mark.XX));
		assertFalse(board.hasCrossDiagonal(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0,0,0, mark);
		board.setField(1,1,1, mark);
		board.setField(2,2,2, mark);
		assertTrue(board.hasCrossDiagonal(Mark.XX));
		assertFalse(board.hasCrossDiagonal(Mark.OO));
		assertTrue(board.hasWinner());
	}

	@Test
	public final void testGameOver() {
		assertFalse(board.hasCrossDiagonal(Mark.XX));
		assertFalse(board.hasCrossDiagonal(Mark.OO));
		Mark mark = Mark.XX;
		board.setField(0,0,0, mark);
		board.setField(1,1,1, mark);
		board.setField(2,2,2, mark);
		assertTrue(board.hasCrossDiagonal(Mark.XX));
		assertFalse(board.hasCrossDiagonal(Mark.OO));
		assertTrue(board.gameOver());
		board.reset();
		assertFalse(board.gameOver());
		for (int i: fields) {
			assertFalse(board.isFull());
			board.setField(i, Mark.XX);
		}
		assertTrue(board.gameOver());
	}

	@Test
	public final void testGetDim() {
		assertEquals(board.getDim(), 3);
	}

	@Test
	public final void testGetSize() {
		assertEquals(board.getSize(), 3 * 3 * 3);
	}

	@Test
	public final void testFall() {
		assertEquals(board.fall(1+9), 1);
	}

}
