package cf.server;

import cf.Protocol;
import cf.model.Board;
import cf.model.Mark;

public class HumanPlayer extends Player {

	
	private ClientHandler handler;
    // -- Constructors -----------------------------------------------

    /*@
       requires mark != null;
       ensures this.getMark() == mark;
    */
    /**
     * Creates a new human player object.
     * 
     */
    public HumanPlayer(ClientHandler handler, Mark mark) {
        super(handler.getUsername(), mark);
        this.handler = handler;
    }

    // -- Queries ----------------------------------------------------
    /**
     * Returns the clienthandler which belongs to the player
     * @return ClientHandler object of player.
     */
    public ClientHandler getHandler() {
    	return handler;
    }
    
    // -- Commands ---------------------------------------------------

    /*@
       requires board != null;
     */
    /**
     * Asks the user to input the field where to place the next mark. This is
     * done using the standard input/output. \
     * 
     * @param board the game board
     * @return the player's chosen field
     */
    public void requestMove(Player currentPlayer, Board board) {
    	handler.writeOutput(Protocol.REQUESTMOVE + Protocol.DELIMITER + currentPlayer.getName());
    }
}