package connectfour;

import java.util.HashSet;
import java.util.Set;

public class NaiveStrategy implements Strategy {

	private String name;
	private String[] computerNames = {"Henk", "Toos", "Frans", "Lisa", "Emma",
			"Ide", "Daniel", "Naomi", "Anne", "Piet", "Arend", "Tom"};
	
	public NaiveStrategy() {
		this.name = computerNames[(int) (Math.random()*computerNames.length)];
	}
	
	@Override
	public String getName() {
		return this.name;
	}

	@Override
	public int determineMove(Board board, Mark mark) {
		Set<Integer> set = new HashSet<Integer>();
		// Add all empty fields to a set.
		for (int i = 0; i < board.getSize(); i++) {
			if (board.isEmptyField(i)) {
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
