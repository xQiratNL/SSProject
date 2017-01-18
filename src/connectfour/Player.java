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
 
    /*@
    	requires board != null & !board.isFull();
    	requires move < board.getDim() * board.getDim();
     */
    /**
     * Makes a move fall. e.g. gets the fallen position for a move.
     * 
     * @param board the current board
     * @param move	the move on the x,y plane (index)
     */
    public static int fall(Board board, int move) {
		int[] xyz = board.coordinates(move);
		int zcoord = 0;
		boolean valid = board.isValidMove(xyz[0], xyz[1], zcoord);
		while (!valid) {
			valid = board.isValidMove(xyz[0], xyz[1], (++zcoord));
		}
		
    	return board.index(xyz[0], xyz[1], zcoord);
    }
    
}
