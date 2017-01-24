package connectfour;

import java.util.HashSet;
import java.util.Set;

public class GeniusStrategy extends Thread implements Strategy {

	private String name;
	private String[] computerNames = {"Tariq", "Rutger"};
	
	public GeniusStrategy() {
		this.name = computerNames[(int) (Math.random()*computerNames.length)];
	} 
	
	@Override
	public String getStrategyName() {
		return this.name;
	}

	@Override
	public int determineMove(Board board, Mark mark) {
		//set move on no clue
		int move = new SmartStrategy().determineMove(board, mark);
		
		Set<Integer> possibleMoves = new HashSet<Integer>();
		for (int i = 0; i < board.getDim() * board.getDim(); i++) {
			possibleMoves.add(Player.fall(board, i));
		}
		
		for (int field: possibleMoves) {
			Board boardCopy = board.deepCopy();
			boardCopy.setField(field, mark);
			if (determineWinner(boardCopy, mark) == mark) {
				return field;
			}
		}
		
		//TODO: help!!!
		return move;
	}
	
	public Mark determineWinner(Board board, Mark mark) {
		if (board.isWinner(mark)) {
			return mark;
		} else if (board.isWinner(mark.other())) {
			return mark.other();
		} else {
			board.
			determineMove()
		}
	}

}
