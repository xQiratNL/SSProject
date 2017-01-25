package connectfour;

public class ComputerPlayer extends Player {

	private Strategy strategy;
	private Mark mark;
	
    // -- Constructor -----------------------------------------------
    /**
     * Creates a new ComputerPlayer object.
     * 
     */	
	public ComputerPlayer(Mark mark, Strategy strategy) {
		super(strategy.getStrategyName(), mark);
		this.strategy = strategy;
		this.mark = mark;
	}
	
	public ComputerPlayer(Mark mark) {
		super("Computer", mark);
		this.strategy = new NaiveStrategy();
	}

    /**
     * Determines the field for the next move.
     * 
     * @param board the current game board
     * @return the player's choice
     */
	public int determineMove(Board board) {
		return fall(board, strategy.determineMove(board, mark));
	}
}
