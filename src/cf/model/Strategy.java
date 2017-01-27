package cf.model;

public interface Strategy {
	
	/**
	 * @return name of the strategy
	 */
	public String getStrategyName();

	/**
	 * Determines a move in xy-plane for a given mark on a board.
	 * @param board, current board
	 * @param mark of player that should make a move
	 * @return index of the field the move should be made on.
	 */
	public int determineMove(Board board, Mark mark);
	
}
