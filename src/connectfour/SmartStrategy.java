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
		while (setMove == -1 && players...) {
			for (Integer s : set) {
				bCopy = board.deepCopy();
				bCopy.setField(s, m.other());
				if (bCopy.hasWinner()) {
					setMove = s;
					break;
				}
			}			
		}

		// Opponent cannot win, so make smartest move

		return setMove;
	}

}
