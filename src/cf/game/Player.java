package cf.game;

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
	
    
    // -- Commands ---------------------------------------------------
 
    /*@
    	requires board != null & !board.isFull();
    	requires move < board.getDim() * board.getDim();
     */
    /**
     * Makes a move fall. e.g. gets the fallen position for a move.
     * 
     * @param board the current board
     * @param move	the move in the x,y plane (index)
     * 
     * @return the index of the fallen place, or -1 if the vertical bar is full already and no move is possible here.
     */
    public static int fall(Board board, int move) {
		int[] xyz = board.coordinates(move);
		int zcoord = 0;
		boolean valid = board.isValidMove(xyz[0], xyz[1], zcoord);
		while (!valid && zcoord < board.getDim() - 1) {
			valid = board.isValidMove(xyz[0], xyz[1], (++zcoord));
		}
		if (valid) {
    		return board.index(xyz[0], xyz[1], zcoord);
		} else {
			return -1;
		}
    }
    
}
