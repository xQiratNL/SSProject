package cf.server;

import cf.model.Board;
import cf.model.Mark;
import cf.model.SmartStrategy;
import cf.model.Strategy;

public class ComputerPlayer extends Player {

	private Strategy strategy;
	
    // -- Constructor -----------------------------------------------
    /**
     * Creates a new computerplayer object with the given mark, and given strategy.
     * @param mark, mark to give to player.
     * @parm strategy, strategy that computerplayer should use, to determine moves.
     */	
	public ComputerPlayer(Mark mark, Strategy strategy) {
		super(strategy.getStrategyName(), mark);
		this.strategy = strategy;
	}
	
	/**
	 * Creates a new computerplayer object with the given mark, and gives it a naive strategy.
	 * @param mark, mark to give to player.
	 */
	public ComputerPlayer(Mark mark) {
		super("Computer", mark);
		this.strategy = new SmartStrategy();
	}

    /**
     * Determines the field for the next move.
     * 
     * @param board the current game board
     * @return the player's choice
     */
	public int determineMove(Board board) {
		return board.fall(strategy.determineMove(board, super.getMark()));
	}
}
