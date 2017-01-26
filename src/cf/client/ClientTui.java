package cf.client;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.HashSet;
import java.util.Scanner;
import java.util.Set;

import cf.game.Board;
import cf.game.Mark;
import cf.game.Player;
import cf.game.SmartStrategy;
import cf.game.Strategy;
import cf.Protocol;

public class ClientTui implements Runnable {
	private BufferedWriter out;
	private Socket sock;
	public boolean usernameSet = false;
	public String username;
	public Mark myMark;
	public Set<String> availableCommands = new HashSet<>();
	public int dimension = Protocol.DIM; // default dimension
	private Board boardTui; // a copy of the board in Client to calculate fallen pieces.
	public boolean isClientComputer = false;
	private static Strategy STRATEGY = new SmartStrategy();

    /*@
		requires sock != null
    */
	/**
	 * Adds the socket to this clientTui.
	 * 
	 * @param sock
	 */
	public void setSocket(Socket sock) {
    	try {
			out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			printLine("ERROR: Cannot handle output stream!");
		}
    	this.sock = sock;	
	}
	
    /*@
		ensures \result != null;
		ensures \result instanceof Integer;
     */
	/**
     *	Get's input from the user to get a port number for the server
     */	
	public int askPort() {
		int portnumber = Protocol.PORTNUMBER;
		@SuppressWarnings("resource") // you don't want to close system.in since it can't be opened again.
		Scanner in = new Scanner(System.in);
		boolean correctInput = false;
		do {
			System.out.print("Enter port number (default " + Protocol.PORTNUMBER + "):");
			String input = in.nextLine();
			try {
				correctInput = true;
				if (!input.isEmpty()) {
					portnumber = Integer.parseInt(input);
				}
			} catch (NumberFormatException e) {
				printLine("Please enter a valid portnumber.");
				correctInput = false;
			}
		} while (!correctInput);
		return portnumber;
	}

    /*@
		ensures \result != null;
		ensures \result instanceof String;
     */
	/**
     *	Get's input from the user to get a host for the server
     */	
	public String askHost() {
		String host = "localhost";
		@SuppressWarnings("resource") // you don't want to close system.in since it can't be opened again.
		Scanner in = new Scanner(System.in);
		System.out.print("Enter host (default " + host + "):");
		String input = in.nextLine();
		if (!input.isEmpty()) {
			host = input;	
		}
		return host;
	}

    /*@
		requires b != null;
     */
	/**
     *	Makes a copy of the board in the Client class and sets this board to that same board.
     *	This is used to make calculations, like falling, in this class upon the play board.
     *
     *	@param board The board of the Client.
     */
	public void copyBoard(Board b) {
		boardTui = b;
	}
	
    /*@
		requires command != null;
		ensures availableCommands.contains(command);
     */
	/**
     *	Adds a new command to the availableCommands field. This fields keeps track
     *	of all the available commands for the client at a very moment.
     *
     *	@param command The command to be added.
     *	@param [command 2]
     *	@param [command 3]
     *	@param ...
     */
	public void addCommands(String... command) {
		for (String c: command) {
			availableCommands.add(c);
		}
	}
	
    /*@
		requires command != null;
		ensures !availableCommands.contains(command);
     */
	/**
     *	Adds a new command to the availableCommands field. This fields keeps track
     *	of all the available commands for the client at a very moment.
     *
     *	@param command	The command to be added.
     *	@param [command 2]
     *	@param [command 3]
     *	@param ...
     *	@return 		true if the commands successfully have been removed. False otherwise.
     */
	public void removeCommands(String... command) {
		for (String c: command) {
			availableCommands.remove(c);
		}
	}
	
	
	/**
     * Reads a string from the console and sends this string over
     * the socket-connection to the ClientTui process.
     * On "exit" the method ends
     */
	@Override
	public void run() {
		String input2 = "";
		printLine("Do you want to play as a human or as a computer? (usage: human/computer)");
		while ( !(input2.equals("human") || input2.equals("computer")) ) {
			input2 = readString();
			if (input2.equals("human")) {
				this.isClientComputer = false;
			} else if (input2.equals("computer")) {
				this.isClientComputer = true;
			} else {
				printLine("Incorrect usage (" + input2 + "). Type 'human' or 'computer'.");
			}
		}
		
		System.out.print("Hi there! Please enter your username: ");
		//TODO: make hello command automated: check if chat/leaderboard/... is enabled and apply that to the HELLO method
		String input = null;
    	while (input == null || !input.equals("exit")) {
			input = readString();
			try {
				if (!usernameSet) {		
					out.write("HELLO;" + input);
					out.newLine();
					out.flush();
					username = input;
					
				} else if (!input.equals("exit") && !(isClientComputer && availableCommands.contains("move"))) {
					// prefents handling input if the 'user' is a computerplayer
					input = reformInput(input);
					if (input != null) {
						out.write(input);
						out.newLine();
						out.flush();
						printLine("Command has been send (" + input + ")");
					}
				}
			} catch (IOException e) {
				printLine("ERROR: Socket is closed!");
			}
		}
    	System.exit(0);

	}
	
    /**
     * Makes a move as a computer player on behalf of the client.
     */	
	public void makeMove() {
		try {
        	int d = Player.fall(boardTui, STRATEGY.determineMove(boardTui, myMark));
        	int[] coords = boardTui.coordinates(d);
        	String moveCommand = "MAKEMOVE" +Protocol.DELIMITER + coords[0] + Protocol.DELIMITER + coords[1] + Protocol.DELIMITER + coords[2];
			out.write(moveCommand);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			printLine("ERROR: Cannot handle output stream!");
		}

	}
	
    /**
     * Changes input given by the user in the TUI to a readable command for the server.
     * 
     * @param input input to handle.
     * @return
     */
    private String reformInput(String input) {        
    	boolean available = false;
    	for (String c : availableCommands) {
    		available = input.startsWith(c);
    		if (available) {
    			break;
    		}	
    	}
    	
    	if (available) {
    		// command is available at this moment!
        	if (input.startsWith("play human ")) {          	
            	Scanner s = new Scanner(input);
            	s.next(); // skip the text. Go to the int.
            	s.next();
            	int d = s.nextInt();
            	input = "PLAY" +Protocol.DELIMITER+ "HUMAN" +Protocol.DELIMITER +d;
            	this.dimension = d;
            	s.close();
            } else if (input.equals("play human")) {
            	input = "PLAY" +Protocol.DELIMITER+ "HUMAN" +Protocol.DELIMITER;
            } else if (input.startsWith("play computer ")) {            	
            	Scanner s = new Scanner(input);
            	s.next(); // skip the text. Go to the int.
            	s.next();
            	int d = s.nextInt();
            	input = "PLAY" +Protocol.DELIMITER+ "COMPUTER" +Protocol.DELIMITER +d;
            	this.dimension = d;
            	s.close();
            } else if (input.equals("play computer")) {
            	input = "PLAY" +Protocol.DELIMITER+ "COMPUTER" +Protocol.DELIMITER;
            } else if (input.startsWith("move ")) {
            	Scanner s = new Scanner(input);
            	s.next(); // skip the text. Go to the int.
            	int d = Player.fall(boardTui, s.nextInt());
            	int[] coords = boardTui.coordinates(d);
            	input = "MAKEMOVE" +Protocol.DELIMITER + coords[0] + Protocol.DELIMITER + coords[1] + Protocol.DELIMITER + coords[2];            	
            	s.close();
            } else if (input.startsWith("ready")) {
            	input = input.replaceFirst("ready", "READY");
            } else if (input.startsWith("decline")) {
            	input = input.replaceFirst("decline", "DECLINE");
            } else if (input.startsWith("hint")) {
            	printLine("Maybe you should enter a mark at " + (new SmartStrategy()).determineMove(boardTui, myMark));
            	input = null;
            }
    	} else {
    		printLine("You cannot use command (" + input + ") right now! Available commands: ");
    		for (String c : availableCommands) {
    			printLine(c);
    		}
    		input = null;
    	}
    
    	return input;
	}

    
	/**
     * Prints the given message.
     */
    public void printLine(String msg) {
		System.out.println(msg);
    }

	/**
     * Closes the connection, the sockets will be terminated.
     */
    public void shutDown() {
		try {
			sock.close();
		} catch (IOException e) {
			printLine("ERROR: Socket is already closed.");
		}
		
    }
    
    /** 
     * read a line from the default input.
     * 
     */
    static public String readString() {
        String antw = null;
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(
                    System.in));
            antw = in.readLine();
        } catch (IOException e) {
        	System.out.println("ERROR: Cannot handle System.in input stream");
        }

        return (antw == null) ? "" : antw;
    }   
    
}
