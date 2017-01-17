package connectfour;

import java.util.HashSet;
import java.util.Set;

public class SmartStrategy implements Strategy {

	private String name;
	private String[] computerNames = {"Tariq", "Rutger"};
	
	public SmartStrategy() {
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
		
		int setMove = -1;
		Board bCopy;
		// check for guaranteed win of this player.
		for (Integer s : set) {
			bCopy = board.deepCopy();
			bCopy.setField(s, mark);
			if (bCopy.hasWinner()) {
				setMove = s;
				break;
			}
		}
		
		// no guaranteed win. Block opponent?
		// loop through all the players and determine if it is possbile that another player wins.
		if (setMove == -1) {
			for (Integer s : set) {
				bCopy = board.deepCopy();
				bCopy.setField(s, mark.other());
				if (bCopy.hasWinner()) {
					setMove = s;
					break;
				}
			}			
		}

		// Opponent cannot win, so check if the middle field is empty.
		if (setMove == -1 && board.isEmptyField((board.getDim()-1)/2, (board.getDim()-1)/2, (board.getDim()-1)/2)) {
			setMove = board.index((board.getDim()-1)/2, (board.getDim()-1)/2, (board.getDim()-1)/2);
		}
		
		// Middle field is not empty, so select a random field.
		if (setMove == -1) {
			int r = (int) (Math.random() * set.size());
			int i = 0;
			for (Integer s : set) {
				if (r == i) {
					setMove = s;
					break;
				}
				i++;
			}
		}
		
		return setMove;
	}

}
