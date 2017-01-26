package cf.game;

import java.util.HashSet;
import java.util.Set;

public class NaiveStrategy implements Strategy {

	private String name;
	private String[] computerNames = {"Henk", "Toos", "Frans", "Lisa", "Emma",
			"Ide", "Daniel", "Naomi", "Anne", "Piet", "Arend", "Tom"};
	
	/**
	 * Constructs a naive strategy with a random name.
	 */
	public NaiveStrategy() {
		this.name = computerNames[(int) (Math.random()*computerNames.length)];
	}
	
	@Override
	/**
	 * Returns name of this strategy.
	 */
	public String getStrategyName() {
		return this.name;
	}

	/**
	 * Determines a random valid move in xy-plane for the given input.
	 */
	@Override
	public int determineMove(Board board, Mark mark) {
		Set<Integer> set = new HashSet<Integer>();
		// Add all empty fields to a set.
		for (int i = 0; i < board.getDim() * board.getDim(); i++) {
			int[] xyz = board.coordinates(i);
			if (board.isEmptyField(xyz[0], xyz[1], board.getDim() - 1)) {
				set.add(i);
			}
		}
		
		// Pick a random field from the set (thus a random empty field)
		int setMove = 0;
		int r = (int) (Math.random() * set.size());
		int i = 0;
		for (Integer s : set) {
			if (r == i) {
		    	setMove = s;
		    	break;
		    }
			i++;
		}
		return setMove;
	}

}
