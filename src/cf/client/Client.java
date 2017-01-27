package cf.client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.Observer;
import java.util.Scanner;

import cf.Protocol;
import cf.model.Board;
import cf.model.Mark;

public class Client implements Observer {
    private static final String USAGE
    = "usage: java connectfour.Client <address>";
    private static final String COMMANDS
	= "play human [dimension] \n"
	+ "play computer [dimension] \n"
	+ "ready \n"
	+ "decline \n"
	+ "move <index> \n"
	+ "hint \n"
	+ "all <text> \n"
	+ "pm <username>;<text> \n"
	+ "game <text>";
    
    private String player1; // first player
    private String player2; // second player
    private Mark myMark; // this player's mark
    private ClientTui tui = new ClientTui();
    private Board board;
    // private ViewerController view; // TODO: 3d view of the game
 
    /**
     * Constructor method
     */
    public Client() {
    	tui.addExtenion(Protocol.EXT_CHAT);
    	this.start();
    }
    
    /**
     * Start method. Starts by asking for a host and portnumber. With these given the method
     * tries to create a socket with the specified data. When the socket is made the TUI is put
     * into a seperate thread and this method continues the monitoring of the inputStream.
     */
    public void start() {
    	InetAddress addr = null;
    	Socket sock = null;
    	BufferedReader in;	
    	String host = "localhost";
    	// try to open a Socket to the server
    	int pn = Protocol.PORTNUMBER; // portnumber
    	boolean sockAccepted = false;
    	while (!sockAccepted) {
    		
        	while (addr == null) {
        		try {
        			host = tui.askHost();
        			addr = InetAddress.getByName(host);
        		} catch (UnknownHostException e) {
        			tui.printLine(USAGE);
        			tui.printLine("ERROR: host " + host + " unknown. Try again.");
        			// System.exit(0);
        		}
        	} 		
    		
    		try {
    			pn = tui.askPort();
    			sock = new Socket(addr, pn);
    			tui.printLine("Connected to " + addr + ":" + pn + " \n");
    			sockAccepted = true;
    		} catch (Exception e) {
    			tui.printLine("ERROR: could not create a socket on " + addr
    					+ " and port " + pn);
    			addr = null;
    		}
    	}
    	
        // create ClientTui object in a new thread and start the two-way communication.
    	// The new thread is created to maintain one process: the output.
    	//tui = new ClientTui(sock);
    	tui.setSocket(sock);
        Thread streamInputHandler = new Thread(tui);
        streamInputHandler.start();
        
        // Handle all incoming communication: the input.
        try {
			in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			while (!sock.isClosed()) {
				try {
					if (in.ready()) {	
						processInput(in.readLine());
					}
				} catch (IOException e) {
					tui.printLine("Cannot read line!");
				}
			}   	
		} catch (IOException e) {
			tui.printLine("ERROR: Inputstream cannot be handled!");
		}
    }
    
    
    /**
     * Method for processing input from the server.
     * 
     * @param input The input message from the server.
     */
    public void processInput(String input) {
    	Scanner scanner = new Scanner(input);
    	scanner.useDelimiter(Protocol.DELIMITER);
    	String command = scanner.next();
    	switch (command) {
    		
    		// Connect to a server:
    		case Protocol.HELLO:
    			tui.printLine("Succesfully connected to the server with " + (scanner.hasNext() ? scanner.next() : "no extensions") + (scanner.hasNext() ? scanner.next() : "") + (scanner.hasNext() ? scanner.next() : "") + (scanner.hasNext() ? scanner.next() : "") + " enabled! \n"
    					+ "Use 'play human [dimension]' or 'play computer [dimension]' to begin a game agains a human player or a computer. \n\n");
    			tui.usernameSet = true;
    			tui.addCommands("play human", "play computer", "exit", "all", "pm");
    			break;
    		case Protocol.ERROR_USERNAME_TAKEN:
    			System.out.print("This username is already in use, please enter another username: ");
    			break;
    		
    		// Starting a game
    		case Protocol.WAIT:
    			tui.printLine("You are currently waiting for a game...");
    			tui.removeCommands("play human", "play computer");
    			//TODO: maybe add the command Decline? This way the user can stop waiting.
    			break;
    		case Protocol.READY:
    			player1 = scanner.next();
    			player2 = scanner.next();
    			String otherPlayer = player1;
    			myMark = Mark.OO;
    			if (player1.equals(tui.username)) {
    				otherPlayer = player2;
    				myMark = Mark.XX;
    			}
    			tui.printLine("You have entered a game with " + otherPlayer + ". Are you ready? (usage: ready/decline)");
    			tui.removeCommands("play human", "play computer");
    			tui.addCommands("ready", "decline");
    			board = new Board(tui.dimension);
    			board.addObserver(this);
    			tui.printLine("game started on a board with DIM " + tui.dimension);
    			tui.copyBoard(board);
    			tui.myMark = this.myMark;
    			// view = new ViewerController();
    			break;
    		
    		// Playing a game
    		case Protocol.REQUESTMOVE:
				tui.removeCommands("ready", "decline");
				tui.addCommands("move", "hint", "game");
    			String userInTurn = scanner.next();
    			if (userInTurn.equals(tui.username)) {
    				if (tui.isClientComputer) {
    					tui.makeMove();
    				} else {
    					tui.printLine("It is your turn! Please make a move! (usage: move <index>)");
    				}
    			} else {
    				tui.printLine("It is " + userInTurn + "'s turn! Please wait for your turn...");
    			}
    			break;
    		case Protocol.SETMOVE:
    			String userInTurn1 = scanner.next();
    			tui.printLine(userInTurn1 + " made a move.");
    			if (userInTurn1.equals(tui.username)) {
    				board.setField(scanner.nextInt(), scanner.nextInt(), scanner.nextInt(), myMark);
    			} else {
    				board.setField(scanner.nextInt(), scanner.nextInt(), scanner.nextInt(), myMark.other());
    			}
    			tui.copyBoard(board);
    			break;
    		case Protocol.ERROR_INVALID_MOVE:
    			tui.printLine("This is an invalid move! Please try again.");
    			break;
    		case Protocol.ERROR_NOT_YOUR_TURN:
    			tui.printLine("Hold on there, cowboy! It isn't your turn yet!");
    			break;
    		case Protocol.GAMEOVER:
    			if (scanner.hasNext()) {
    				tui.printLine("Game over! User " + scanner.next() + " has won the game");
    			} else {
    				tui.printLine("Game over! Ended in a draw.");
    			}
    			tui.removeCommands("move", "decline", "ready", "hint", "game");
    			tui.addCommands("play human", "play computer");
    			break;
    		case Protocol.ERROR_USER_QUIT:
    			tui.printLine("User " + scanner.next() + " is a chicken. He cowarded out!");
    			tui.removeCommands("move", "hint", "game");
    			tui.addCommands("play human", "play computer");
    			break;
    		
    			
    		// ====== OPTIONALS ======
    		// Chat
    		case Protocol.BROADCAST:
    			tui.printLine("ALL| " + scanner.next() + ": " + scanner.next());
    			break;
    		case Protocol.WHISPER:
    			tui.printLine("DM| " + scanner.next() + ": " + scanner.next());
    			break;
    		case Protocol.CHATUSERS:
    			String users = "";
    			while (scanner.hasNext()) {
    				users += scanner.next() + ", ";
    			}
    			users.substring(0,users.length()-2);
    			tui.printLine("List of all users:" + users);
    			break;
    		case Protocol.GAMECHAT:
    			// GAMECHAT <username> <text> (Not well defined in protocol)
    			tui.printLine("GAME| " + scanner.next() + ": " + scanner.next());
    			break;
    		case Protocol.ERROR_USER_HAS_NO_CHAT:
    			tui.printLine("It seems that this user has no chat.");
    			break;
    		case Protocol.ERROR_USER_NOT_FOUND:
    			tui.printLine("The server can't find this player.");
    			break;
    		case Protocol.ERROR_NOT_IN_GAME:
    			tui.printLine("You are currently not in a game, so gamechat is not available.");
    			break;
    		
    		// Challenge
    		
    		// Leaderboard
    			
    		// Password
    		
    		// Other
    		case Protocol.ERROR_COMMAND_NOT_RECOGNIZED:
    			tui.printLine("Command has not been recognized by the server! Please use one of the commands below:");
    			tui.printLine(COMMANDS);
    			break;
    	}
    	
    	scanner.close();
    }
    
    @Override
	public void update(Observable o, Object arg) {
    	tui.printLine(board.toString());
	}
    
    /** Starts a Client application. */
    public static void main(String[] args) {
    	new Client();
    }

    
}
