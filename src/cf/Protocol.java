package cf;

/**
 * This interface describes the main variables of the protocol need to make a
 * between the client and the server.
 * 
 * @author Carmen Burghardt / Gereon Mendler (Modifications)
 * @version 1.2 (25-01-2017),Eclipse: 4.6.1
 */

// When a message contains <> you should fill it in yourself. When a message
// contains [] itâ€™s optional. E.g. connecting with the server with username
// Pietje18 and extension challenge would look like: HELLO + DELIMITER +
// Pietje18 + DELIMITER + EXT_CHALLENGE

public interface Protocol {
	
	public static final String DELIMITER = ";";
	
    // The dimension of the field of the tournament
    public static final int DIM = 4;
	
	// What about unexpected commands?
	/**
	 * If the server gets a command that is not expected, for example MAKEMOVE when HELLO is needed first,
	 * it sends this message together with the expected keyword, thus in that example: 
	 * 
	 * ERROR_UNEXPECTED;<Expected command>;[other expectations]
	 */
	public static final String ERROR_UNEXPECTED = "ERROR_UNEXPECTED"; 
	
	public static final String ERROR_COMMAND_NOT_RECOGNIZED = "ERROR_COMMAND_NOT_RECOGNIZED";

	
	/* --------------------------- Connect to server ----------------------- */
	/**
	 * 1.Client handshakes with server,via the port number 
	 * 2.Client sends user name and the extra extensions to the server 
	 * HELLO <username> [EXT_CHALLENGE] [EXT_CHAT] [EXT_LEADERBOARD] [EXT_PASSWORD] 
	 * 3.Server accepts user name or sends an error that the user name is taken 
	 * HELLO [EXT_CHALLENGE] [EXT_CHAT] [EXT_LEADERBOARD] [EXT_PASSWORD]
	 * ERROR_USERNAMETAKEN
	 */
	public static final int PORTNUMBER = 1337;
	//1. and 2.
	public static final String HELLO = "HELLO";
	public static final String EXT_CHAT = "EXT_CHAT";
	public static final String EXT_CHALLENGE = "EXT_CHALLENGE";
	public static final String EXT_LEADERBOARD = "EXT_LEADERBOARD";
	public static final String EXT_PASSWORD = "EXT_PASSWORD";
	// 3. Exception
	public static final String ERROR_USERNAME_TAKEN = "ERROR_USERNAME_TAKEN"; 

	/* --------------------------- Start a game --------------------------- */
	/**
	 * During the lecture we discussed the possibility to play with several
	 * players, playing with 2 players is enough, therefore the protocol has
	 * been changed
	 */
	
	/**
	 * 1. Player chooses with what kind of user he likes to play -Human player
	 * to human player 
	 * PLAY HUMAN [DIM] 
	 * -Human player to computer player 
	 * PLAY COMPUTER [DIM] 
	 * 2. Server: sends wait, when the player has to wait for
	 * another player 
	 * WAIT 
	 * 3. Server: sends ready when the game can start (this also happens when playing with a computer player)
	 * READY <username1> <username2> 
	 * 4. Client: responds with READY when they want to
	 * start, DECLINE otherwise (in this case the client will get back to the lobby)
	 * READY 
	 * DECLINE 
	 * 5. Server: requests a move from
	 * the user whose turn it is, this message is send to both players
	 * REQUESTMOVE <username> 
	 * 6. Client: Make move with the coordinates 
	 * MAKEMOVE <x> <y> <z> 
	 * 7. Server will either send setmove when the move was valid to
	 * everyone; invalid move when it was invalid to the user, or not your turn
	 * when it was not his turn. 
	 * SETMOVE <username> <x> <y> <z>
	 * ERROR_INVALIDMOVE <x> <y> <z> 
	 * ERROR_NOTYOURTURN 
	 * 8. Server: when the game is not over, the server requests a new move. When the game is over its
	 * told to both players, and when there is a winner this name is added.
	 * GAMEOVER [username of winner] 
	 * When someone quits the game an error is
	 * send and user moves back to the lobby 
	 * ERROR_USERQUIT <username of quiter>
	 * The timeout is set on 20 seconds.
	 */
	// 1.
	public static final String PLAY = "PLAY";
	public static final String HUMAN = "HUMAN";
	public static final String COMPUTER = "COMPUTER";
	// 2.
	public static final String WAIT = "WAIT";
	// 3. and 4.
	public static final String READY = "READY";
	public static final String DECLINE = "DECLINE";
	// 5.
	public static final String REQUESTMOVE = "REQUESTMOVE";
	// 6.
	public static final String MAKEMOVE = "MAKEMOVE";
	// 7.
	public static final String SETMOVE = "SETMOVE";
	public static final String ERROR_INVALID_MOVE = "ERROR_INVALID_MOVE"; 
	public static final String ERROR_NOT_YOUR_TURN = "ERROR_NOT_YOUR_TURN"; 
	// 8. (Gameover)
	public static final String GAMEOVER = "GAMEOVER";
	// Exception (Quit)
	public static final String ERROR_USER_QUIT = "ERROR_USER_QUIT"; 

	/*
	 * --------------------------- EXTENSION ----------------------------------
	 */

	/* --------------------------- Chat ---------------------------------- */
	/**
	 * 1.Client sends Broadcast <text> to server 
	 * BROADCAST <text> 
	 * 2.Server broadcast chat 
	 * BROADCAST <user> <text>  
	 * 3.Client whisper to server to the one who requested it 
	 * WHISPER <username> <text> 
	 * 4. Client requests chatuser list
	 * CHATUSERS
	 * 5.Server sends chat users
	 * CHATUSERS <username> [username] 
	 * 6.Client start game chat via server 
	 * GAMECHAT <text > 
	 * 7.Server will support game chat when the user is found,has chat and is in the game,
	 * otherwise is the user not found, or he has no chat or he is not in the game 
	 * GAMECHAT ERROR_USER_NOT_FOUND 
	 * ERROR_USER_HAS_NO_CHAT
	 * ERROR_NOT_IN_GAME
	 */
	
	// 1. and 2.
	public static final String BROADCAST = "BROADCAST";
	// 3.
	public static final String WHISPER = "WHISPER";
	// 4. and 5.
	public static final String CHATUSERS = "CHATUSERS";
	// 6.
	public static final String GAMECHAT = "GAMECHAT";
	// 7.
	public static final String ERROR_USER_NOT_FOUND = "ERROR_USER_NOT_FOUND";
	public static final String ERROR_USER_HAS_NO_CHAT = "ERROR_USER_HAS_NO_CHAT";
	public static final String ERROR_NOT_IN_GAME = "ERROR_NOT_IN_GAME";

	/*
	 * --------------------------- Challenge ----------------------------------
	 */
	/**
	 * 1.Clients sends challenge to a certain other client via server 
	 * CHALLENGE <username> 
	 * 2.Server receives challenge 
	 * CHALLENGED <username> 
	 * 3.The client accept or declines the challenge 
	 * ACCEPT 
	 * DECLINE
	 * 4.If declined the server will cancel the challenge 
	 * CANCELLED <username> 
	 * 5.The client asks for status if challenge not canceled 
	 * STATUS <username> 
	 * 6. Server sent back the status of the user if the user is found,user is not
	 * in an game and the user has option to the challenge function.Otherwise
	 * the server will throw an error. 
	 * STATUS <username> <status> (EG AVAILABLE)
	 * USER_NOT_FOUND_FOR_CHALLENGE ERROR_USER_IN_GAME
	 * ERROR_USER_HAS_NO_CHALLENGE
	 */
	// 1.
	public static final String CHALLENGE = "CHALLENGE";
	// 2.
	public static final String CHALLENGED = "CHALLENGED";
	// 3.
	public static final String ACCEPT = "ACCEPT";
	// DECLINE is initialized earlier
	// 4.
	public static final String CANCELLED = "CANCELLED";
	//5.
	public static final String STATUS = "STATUS";
	public static final String AVAILABLE = "AVAILABLE";
	public static final String NOT_AVAILABLE = "NOT_AVAILABLE"; 
	//6.
	public static final String ERROR_USER_NOT_FOUND_FOR_CHALLENGE = "USER_NOT_FOUND_FOR_CHALLENGE";
	public static final String ERROR_USER_IN_GAME = "ERROR_USER_IN_GAME";
	public static final String ERROR_USER_HAS_NO_CHALLENGE = "ERROR_USER_HAS_NO_CHALLENGE ";
	
	

	/*
	 * --------------------------- Leader board ----------------------------------
	 */
	/**
	 * 1.Client requests leaderboard
	 * LEADERBOARD 
	 * 2.Sever sends leader board, unless command not is not recognized 
	 * LEADERBOARD <username> <points> [usernmae] [points] ... 
	 */

	public static final String LEADERBOARD = "LEADERBOARD";
	

	/*
	 * --------------------------- Password ----------------------------------
	 */
	/**
	 * 1. Server request password 
	 * REQUEST_PASSWORD 
	 * 2. Client sends hash of the password 
	 * PASSWORD<hash of password> 
	 * 3. Server sent if the password is granted. If no access is granted,the access is denied. ACCESGRANTED
	 * ERROR_ACCES_DENIED 
	 * ACCESS_GRANTED
	 * 4. If granted it also will make an account if not
	 * already existing. 
	 * REGISTERED
	 */
	// 1.
	public static final String REQUEST_PASSWORD = "REQUESTPASSWORD";
	// 2.
	public static final String PASSWORD = "PASSWORD";
	// 3.
	public static final String ACCESS_GRANTED = "ACCESGRANTED";
	public static final String ERROR_ACCESS_DENIED = "ERROR_ACCES_DENIED";
	// 4.
	public static final String REGISTERED = "REGISTERED";
}
