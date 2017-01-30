package cf.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import cf.model.*;

public class GeniusStrategyTest {

	Board board;
	Strategy strategy;
	
	@Before
	public void setUp() throws Exception {
		board = new Board(2);
		strategy = new GeniusStrategy(3);
	}

	@Test
	public final void testGeniusStrategy() {
		assertTrue(strategy instanceof Strategy);
		assertTrue(strategy.getStrategyName() instanceof String);
	}

	@Test
	public final void testGetStrategyName() {
		assertTrue(strategy.getStrategyName().equals("Rutger") || strategy.getStrategyName().equals("Tariq"));
	}

	@Test
	public final void testDetermineMove() {
		for (int i = 0; i < 100; i++) {
			int move = strategy.determineMove(board, Mark.XX);
			assertTrue(0 <= move && move < board.getDim() * board.getDim()); //move in xy-plane
		}
	}

}
