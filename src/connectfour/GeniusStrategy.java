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
		
		
		
		return move;
	}

}
