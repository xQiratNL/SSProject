package connectfour;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;

public class Client {
    private static final String USAGE
    = "usage: java connectfour.Client <address>";
    private static final String COMMANDS
	= "play human [dimension] \n"
	+ "play computer [dimension] \n"
	+ "ready \n"
	+ "decline \n"
	+ "move <index>";
    
    private String player1; // first player
    private String player2; // second player
    private Mark myMark; // this player's mark
    private ClientTui tui;
    private Board board;
    
    public Client(String InetAdress) {
    	try {
			this.start(InetAdress);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    }
    
    public void start(String InetAdress) throws IOException {
    	InetAddress addr = null;
    	Socket sock = null;
    	BufferedReader in;
    	
    	// check args[0] - the IP-adress
    	try {
    		addr = InetAddress.getByName(InetAdress);
    	} catch (UnknownHostException e) {
    		System.out.println(USAGE);
    		System.out.println("ERROR: host " + InetAdress + " unknown");
    		System.exit(0);
    	}

    	// try to open a Socket to the server
    	try {
    		sock = new Socket(addr, Protocol.PORTNUMBER);
    	} catch (IOException e) {
    		System.out.println("ERROR: could not create a socket on " + addr
    				+ " and port " + Protocol.PORTNUMBER);
    	}
    	
        // create ClientTui object in a new thread and start the two-way communication.
    	// The new thread is created to maintain one process: the output.
    	tui = new ClientTui(sock);
        Thread streamInputHandler = new Thread(tui);
        streamInputHandler.start();
        
        // Handle all incoming communication: the input.
        in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		while (!sock.isClosed()) {
			try {
				if (in.ready()) {	
					processInput(in.readLine());
				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
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
    			System.out.println("Succesfully connected to the server with " + (scanner.hasNext() ? scanner.next() : "no extensions") + (scanner.hasNext() ? scanner.next() : "") + (scanner.hasNext() ? scanner.next() : "") + (scanner.hasNext() ? scanner.next() : "") + " enabled! \n"
    					+ "Use 'play human [dimension]' or 'play computer [dimension]' to begin a game agains a human player or a computer. \n\n");
    			tui.usernameSet = true;
    			tui.addCommands("play human", "play computer");
    			break;
    		case Protocol.ERROR_USERNAMETAKEN:
    			System.out.print("This username is already in use, please enter another username: ");
    			break;
    		
    		// Starting a game
    		case Protocol.WAIT:
    			System.out.println("You are currently waiting for a game...");
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
    			System.out.println("You have entered a game with " + otherPlayer + ". Are you ready? (usage: ready/decline)");
    			tui.removeCommands("play human", "play computer");
    			tui.addCommands("ready", "decline");
    			board = new Board(tui.dimension);
    			tui.copyBoard(board);
    			break;
    		
    		// Playing a game
    		case Protocol.REQUESTMOVE:
				tui.removeCommands("ready", "decline");
				tui.addCommands("move");
    			String userInTurn = scanner.next();
    			if (userInTurn.equals(tui.username)) {
    				System.out.println(board.toString());
    				System.out.println("It is your turn! Please make a move! (usage: move <index>)");
    			} else {
    				System.out.println("It is " + userInTurn + "'s turn! Please wait for your turn...");
    			}
    			break;
    		case Protocol.SETMOVE:
    			String userInTurn1 = scanner.next();
    			System.out.println(userInTurn1 + " made a move.");
    			if (userInTurn1.equals(tui.username)) {
    				board.setField(scanner.nextInt(), scanner.nextInt(), scanner.nextInt(), myMark);
    			} else {
    				board.setField(scanner.nextInt(), scanner.nextInt(), scanner.nextInt(), myMark.other());
    			}
    			tui.copyBoard(board);
    			break;
    		case Protocol.ERROR_INVALIDMOVE:
    			System.out.println("This is an invalid move! Please try again.");
    			break;
    		case Protocol.ERROR_NOTYOURTURN:
    			System.out.println("Hold on there, cowboy! It isn't your turn yet!");
    			break;
    		case Protocol.GAMEOVER:
    			if (scanner.hasNext()) {
    				System.out.println("Game over! User " + scanner.next() + " has won the game");
    			} else {
    				System.out.println("Game over! Ended in a draw.");
    			}
    			tui.removeCommands("move", "decline", "ready");
    			tui.addCommands("play human", "play computer");
    			break;
    		case Protocol.ERROR_USERQUIT:
    			System.out.println("User " + scanner.next() + " is a chicken. He cowarded out!");
    			tui.removeCommands("move");
    			tui.addCommands("play human", "play computer");
    			break;
    		
    			
    		// ====== OPTIONALS ======
    		// Chat
    		case Protocol.BROADCAST:
    			//do this
    			break;
    		case Protocol.WHISPER:
    			//do this
    			break;
    		case Protocol.CHATUSER:
    			//do this
    			break;
    		case Protocol.GAMECHAT:
    			//do this
    			break;
    		case Protocol.ERROR_USER_HAS_NO_CHAT:
    			//do this
    			break;
    		case Protocol.ERROR_USER_NOT_FOUND:
    			//do this
    			break;
    		case Protocol.ERROR_NOT_IN_GAME:
    			//do this
    			break;
    		
    		// Challenge
    		
    		// Leaderboard
    			
    		// Password
    		
    		// Other
    		case Protocol.ERROR_COMMAND_NOT_RECOGNIZED:
    			System.out.println("Command has not been recognized by the server! Please use one of the commands below:");
    			System.out.println(COMMANDS);
    			break;
    	}
    	
    	scanner.close();
    }
    
    /** Starts a Client application. */
    public static void main(String[] args) {
    	if (args.length != 1) {
    		System.out.println(USAGE);
    		System.exit(0);
    	}
    	new Client(args[0]);
    }
    
}
