package connectfour;

import java.util.HashMap;

/**
 * This interface describes the main variables of the protocol need to make a
 * between the client and the server.
 * 
 * @author Carmen Burghardt 
 * @version 1.1 (11-01-2017),Eclipse: 4.6.1
 */

// When a message contains <> you should fill it in yourself. When a message contains [] it's optional. E.g. connecting with the server with username Pietje18 and extension challenge would look like: HELLO + DELIMITER + â€œPietjeâ€�+ DELIMITER + EXT_CHALLENGE

public interface Protocol {
	
	/* --------------------------- Connect to server -----------------------	 */
	/**
	* 1.Client handshakes with server,via the port number
	* 2.Client sends user name  and the extra extensions to the server
	* HELLO <username> [EXT_CHALLENGE]  [EXT_CHAT] [EXT_LEADERBOARD] [EXT_PASSWORD]
	* 3.Server accepts user name or sends an error that the user name is taken
	* HELLO  [EXT_CHALLENGE] [EXT_CHAT] [EXT_LEADERBOARD] [EXT_PASSWORD]
	* ERROR_USERNAMETAKEN
	*/
	public static final int PORTNUMBER = 1337;
	public static final String USERNAME = "Henkie";
	public static final String EXT_CHAT = "EXT_CHAT";
	public static final String EXT_CHALLENGE = "EXT_CHALLENGE";
	public static final String EXT_LEADERBOARD = "EXT_LEADERBOARD";
	public static final String EXT_PASSWORD = "EXT_PASSWORD";
	public static final String DELIMITER = ";";
	public static final String ERROR_USERNAMETAKEN = "ERROR_USERNAMETAKEN";
	
	
	
	/* --------------------------- Start a game  ---------------------------	 */
	/** During the lecture we discussed the possibility to play with several players, playing with 2 players is enough, therefore the protocol has been changed */
	/**
	* 1. Player chooses with what kind of user he likes to play
	* -Human player to human player
	* PLAY HUMAN [DIM]
	* -Human player to computer player
	* PLAY COMPUTER [DIM]
	* 2. Server: sends wait, when the player has to wait for another player
	* WAIT
	* 3. Server: sends ready when the game can start
	* READY <username1> <username2>
	* 4. Client: responds with ready when they want to start, DECLINE otherwise
	* READY
	* DECLINE
	* 5. Server: requests a move from the user whose turn it is, this message is send to both players
	* REQUESTMOVE <username>
	* 6. Client: Make move with the coordinates
	* MAKEMOVE <x> <y> <z>
	* 7. Server will either send setmove when the move was valid to everyone; invalid move when it was invalid to the user, or not your turn when it was not his turn.
* SETMOVE <username> <x> <y> <z>
* ERROR_INVALIDMOVE <x> <y> <z>
* ERROR_NOTYOURTURN
	* 8. Server: when the game is not over, the server requests a new move. When the game is over its told to both players, and when there is a winner this name is added. 
	* GAMEOVER [username of winner]
	* When someone quits the game an error is send and user moves back to the lobby
	* ERROR_USERQUIT <username of quiter>
	* The timeout is set on 20 seconds.
	*/
	

	public static final String PLAY = "PLAY";
	public static final String HUMAN = "HUMAN";
	public static final String COMPUTER = "computer";
	
	
	public static final String WAIT = "WAIT";
	public static final String READY = "READY";
	public static final String REQUESTMOVE = "REQUESTMOVE";
	
	
	public static final String ERROR_INVALIDMOVE = "ERROR_INVALIDMOVE";
	
	public static final String ERROR_NOTYOURTURN = "ERROR_NOTYOURTURN";
	
	public static final String GAMEOVER = "GAMEOVER";
	public static final String ERROR_USERQUIT = "ERROR_USERQUIT";
	
	public static final String DECLINE = "DECLINE";
	

	/* --------------------------- EXTENSION ----------------------------------	 */


	/* --------------------------- Chat ----------------------------------	 */
	/**
	* 1.Client sends Broadcast <text> to server
	* BROADCAST <text>
	* 2.Server broadcast chat
	* 	BROADCAST <text> <user>
	* 3.Client whisper to server to the ont who requested it
	* WHISPER <username> <text>
	* 4.Server sends chat users
	* CHATUSERS <username> [username]
	* 5. Client receives chatuser
	* CHATUSERS 
	* 6.Client start game chat via server
	* GAMECHAT <text > 	
	* 7.Server will support game chat when the user is found,has chat and is in the game, otherwise is the user not found, or he has no chat
	* or he is not in the game
	* GAMECHAT
	* ERROR_USER_NOT_FOUND 
	* ERROR_USER_HAS_NO_CHAT 
	* ERROR_NOT_IN_GAME
	*/
	
	public static final String TEXT = "TEXT";
	public static final String BROADCAST = "BROADCAST";
	HashMap<String, String> WHISPER = new HashMap<String, String>();
	HashMap<String, String> CHATUSER = new HashMap<String, String>();
	
	public static final String GAMECHAT = "text";
	
	public static final String ERROR_USER_NOT_FOUND = "RROR_USER_NOT_FOUND";
	public static final String ERROR_USER_HAS_NO_CHAT = "ERROR_USER_HAS_NO_CHAT";
	public static final String ERROR_NOT_IN_GAME = "ERROR_NOT_IN_GAME";
	
	
	/* --------------------------- Challenge ----------------------------------	 */
	/**
	* 1.Clients sends challenge to a certain other client via server 
	* CHALLENGE <username>[username]
	* 2.Server receives challenge
	* CHALLENGE <username> [username]
	* 3..The client accept or declines the challenge
	* ACCEPT
	* DECLINED
	* 4.If declined the server cancel the challenge
	* CANCELED <username>
	* 5.The client asks for status if challenge not canceled
	* STATUS <username>
	* 6. Server sent back the status of the user if the user is found,user is not in an game and the user has option to the challenge 
	* function.Otherwise the server will throw and error.
	* STATUS <username> 
	* AVAILABLE [username]
	* USER_NOT_FOUND_FOR_CHALLENGE
	* ERROR_USER_IN_GAME 
	* ERROR_USER_HAS_NO_CHALLENGE
	*/
	public static final String CHALLENGE = "CHALLENGE";
	public static final String USER_NOT_FOUND_FOR_CHALLENGE = "SER_NOT_FOUND_FOR_CHALLENGE";
	public static final String ERROR_USER_IN_GAME = "ERROR_USER_IN_GAME";
	public static final String ERROR_USER_HAS_NO_CHALLENGE = "ERROR_USER_HAS_NO_CHALLENGE ";
	public static final boolean STATUS= true;
	public static final boolean available = true;
	public static final String ACCEPTED = "ACCEPTED";
	public static final String DECLINED = "DECLINED";
	
	
	/* --------------------------- Leader board ----------------------------------	 */
	/**
	* 1.Client sends leader board to the server  
	* LEADERBOARD
	* 2.Sever receives leader board, unless command not is not recognized
	* LEADERBOARD <username> <points>
	* ERROR_COMMAND_NOT_REGONIZED
	*/
	
	public static final String LEADERBORD = "LEADERBORD";
	public static final String ERROR_COMMAND_NOT_REGONIZED = "ERROR_COMMAND_NOT_REGONIZED";
	
	/* --------------------------- Password ----------------------------------	 */
	/**
	* 1. Server request password
	*REQUESTEDPASSWORD
	* 2. Client sends hash of the password
	*  PASSWORD<hash of password>
	* 3. Server sent if the password is granted. If no
	* access is granted,the access is denied.
	* ACCESGRANTED
	* ERROR_ACCES_DENIED
	* 4. If granted it also will make an account if not already existing.
	* REGISTERED 
	* REGISTERED
	*/
	public static final String REQUESTPASSWORD= "request password";
	public static final String PASSWORD = "HITHERE";
	public static final String ACCESGRANTED = "ACCESGRANTED";
	public static final String ERROR_ACCES_DENIED = "ERROR_ACCES_DENIED";
	public static final String REGISTERED = "REGISTERED";
}
	

