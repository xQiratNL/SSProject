package cf.game;

import java.util.HashSet;
import java.util.Set;

public class SmartStrategy implements Strategy {

	private String name;
	private String[] computerNames = {"Tariq", "Rutger"};
	
	public SmartStrategy() {
		this.name = computerNames[(int) (Math.random()*computerNames.length)];
	}
	
	@Override
	public String getStrategyName() {
		return this.name;
	}

	@Override
	public int determineMove(Board board, Mark mark) {
		Set<Integer> set = new HashSet<Integer>();
		// Add all empty fields to a set.

	//	for (int i = board.getSize() - (board.getDim() * board.getDim()); i < board.getSize(); i++) {
		for (int i = 0; i < board.getDim() * board.getDim(); i++) {
			int[] xyz = board.coordinates(i);
			if (board.isEmptyField(xyz[0], xyz[1], board.getDim() - 1)) {
				set.add(i);
			}
		}
		
		int setMove = -1;
		Board bCopy;
		// check for guaranteed win of this player.
		for (Integer s : set) {
			bCopy = board.deepCopy();
			int field = Player.fall(bCopy, s);
			bCopy.setField(field, mark);
			if (bCopy.hasWinner()) {
				setMove = s;
				break;
			}
		}
		
		// no guaranteed win. Block opponent?
		// loop through all the players and determine if it is possible that another player wins.
		if (setMove == -1) {
			for (Integer s : set) {
				bCopy = board.deepCopy();
				int field = Player.fall(bCopy, s);
				bCopy.setField(field, mark.other());
				if (bCopy.hasWinner()) {
					setMove = s;
					break;
				}
			}			
		}

		// Opponent cannot win, so check if the middle field is empty.
		if (setMove == -1 && board.isEmptyField((board.getDim()-1)/2, (board.getDim()-1)/2, (board.getDim()-1)/2)) {
			setMove = board.index((board.getDim()-1)/2, (board.getDim()-1)/2, 0);
			System.out.println("evaluating middle fields");
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
			System.out.println("random move");
		}
		
		return setMove;
	}

}