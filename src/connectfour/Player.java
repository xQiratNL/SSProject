package connectfour;

public abstract class Player {

    // -- Instance variables -----------------------------------------

	private String name;
	private Mark mark;

    // -- Constructor -----------------------------------------------

    /*@
       requires name != null;
       requires mark != null;
       ensures this.getName() == name;
       ensures this.getMark() == mark;
     */
    /**
     * Creates a new Player object.
     * 
     */
	public Player(String name, Mark mark) {
		this.name = name;
		this.mark = mark;
	}

    /*@
    	requires name != null;
    	requires mark != null;
    	requires strategy != null;
    	ensures this.getName() == name;
    	ensures this.getMark() == mark;
     */
	// If the player has a smart strategy, then the name of this ComputerPlayer is changed to Tariq or Rutger :)
	public Player(String name, Mark mark, Strategy strategy) {
		if (strategy.getName().equals("Smart")) {
			int nameChoice = (int) Math.floor(Math.random() * 2);
			if (nameChoice == 0) {
				this.name = "Tariq";
			} else {
				this.name = "Rutger";
			}
		} else {
			this.name = name;
		}
		this.mark = mark;
	}
	
    // -- Queries ----------------------------------------------------

    /**
     * Returns the name of the player.
     */
    /*@ pure */ public String getName() {
		return name;
	}
    
    /**
     * Returns the mark of the player.
     */	
    /*@ pure */ public Mark getMark() {
		return mark;
	}
	
    /*@
    	requires board != null & !board.isFull();
    	ensures board.isField(\result) & board.isEmptyField(\result);
    */
    /**
     * Determines the field for the next move.
     * 
     * @param board the current game board
     * @return the player's choice
     */
    public abstract int determineMove(Board board);
    
    // -- Commands ---------------------------------------------------

    /*@
       requires board != null & !board.isFull();
     */
    /**
     * Makes a move (index, from determineMove(board)) on the board.
     * 
     * @param board the current board
     */
    public void makeMove(Board board) {
        int index = determineMove(board);
        board.setField(index, getMark());
    }
    
}
