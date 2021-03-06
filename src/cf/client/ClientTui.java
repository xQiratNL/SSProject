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

import cf.Protocol;
import cf.model.Board;
import cf.model.GeniusStrategy;
import cf.model.Mark;
import cf.model.SmartStrategy;
import cf.model.Strategy;

public class ClientTui implements Runnable {
	private BufferedWriter out;
	private Socket sock;
	public boolean usernameSet = false;
	public String username;
	public Mark myMark;
	public Set<String> availableCommands = new HashSet<String>();
	public int dimension = Protocol.DIM; // default dimension
	private Board boardTui; // a copy of the board in Client to calculate fallen pieces.
	public boolean isClientComputer = false;
	private static Strategy STRATEGY = new GeniusStrategy(); // the strategy used if the client plays as a computer.
	private static String EXTENTIONS = "";
    private static final String COMMANDS
	= "play human [dimension] \t\t play a game against another human \n"
	+ "play computer [dimension] \t play a game agains a computer player \n"
	+ "ready \t\t\t\t accepts an incoming game \n"
	+ "decline \t\t\t declines an incoming game \n"
	+ "move <index> \t\t\t sets a move on the board \n"
	+ "hint \t\t\t\t request a hint from the computer \n"
	+ "all <text> \t\t\t sent a chat message to all the active chat users \n"
	+ "pm <username>;<text> \t\t sends a personal message to <username> \n"
	+ "game <text> \t\t\t sends a message to all the players in your current game \n"
	+ "chatusers \t\t\t prints a list of all users with chat enabled \n"
	+ "help \t\t\t\t prints this message";
	
    /*@
		requires sock != null;
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
		requires ext != null;
     */
	/**
     *	Sets the EXTENSIONS field to a new value including the added extension.
     */	
	public void addExtenion(String ext) {
		EXTENTIONS += ext + ";";
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
		printLine("Do you want to play as a human or as a computer? (usage: human/computer <time>)");
		while ( !(input2.equals("human") || input2.startsWith("computer")) ) {
			input2 = readString();
			if (input2.equals("human")) {
				this.isClientComputer = false;
			} else if (input2.startsWith("computer")) {
				this.isClientComputer = true;
				if (STRATEGY instanceof GeniusStrategy) { // sets the time of the strategy to the parameter.
					((GeniusStrategy) STRATEGY).setThinkTime(Integer.parseInt(input2.replaceAll("\\D+","")));
				}
			} else {
				printLine("Incorrect usage (" + input2 + "). Type 'human' or 'computer <time>'.");
			}
		}
		
		System.out.print("Hi there! Please enter your username: ");
		String input = null;
    	while (input == null || !input.equals("exit")) {
			input = readString();
			try {
				if (!usernameSet) {		
					out.write("HELLO;" + input + Protocol.DELIMITER + EXTENTIONS);
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
        	int d = boardTui.fall(STRATEGY.determineMove(boardTui, myMark));
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
            	if (s.hasNextInt()) {
            		int d = s.nextInt();
            		input = Protocol.PLAY +Protocol.DELIMITER+ Protocol.HUMAN +Protocol.DELIMITER +d;
            		this.dimension = d;
            	} else {
            		this.dimension = Protocol.DIM;
            	}
            	s.close();
            } else if (input.equals("play human")) {
            	input = Protocol.PLAY +Protocol.DELIMITER+ Protocol.HUMAN +Protocol.DELIMITER;
            } else if (input.startsWith("play computer ")) {            	
            	Scanner s = new Scanner(input);
            	s.next(); // skip the text. Go to the int.
            	s.next();
            	if (s.hasNextInt()) {
            		int d = s.nextInt();
            		input = Protocol.PLAY +Protocol.DELIMITER+ Protocol.COMPUTER +Protocol.DELIMITER +d;
            		this.dimension = d;
            	} else {
            		this.dimension = Protocol.DIM;
            	}
            	s.close();
            } else if (input.equals("play computer")) {
            	input = "PLAY" +Protocol.DELIMITER+ Protocol.COMPUTER +Protocol.DELIMITER;
            } else if (input.startsWith("move ")) {
            	Scanner s = new Scanner(input);
            	s.next(); // skip the text. Go to the int.
            	if (s.hasNextInt()) {
            		int d = boardTui.fall(s.nextInt());
            		int[] coords = boardTui.coordinates(d);
            		input = Protocol.MAKEMOVE +Protocol.DELIMITER + coords[0] + Protocol.DELIMITER + coords[1] + Protocol.DELIMITER + coords[2];            	
            	} else {
            		printLine("You didn't specify the index of the move. (Usage: move <index>)");
            		input = null;
            	}
            	s.close();
            } else if (input.startsWith("ready")) {
            	input = input.replaceFirst("ready", Protocol.READY);
            } else if (input.startsWith("decline")) {
            	input = input.replaceFirst("decline", Protocol.DECLINE);
            } else if (input.startsWith("hint")) {
            	printLine("Maybe you should enter a mark at " + (new SmartStrategy()).determineMove(boardTui, myMark));
            	input = null;
            } 
            
            
            else if (input.startsWith("all ")) {
            	// Chat optional
            	// Changes the first words with the readable for the server
            	input = input.replaceFirst("all ", Protocol.BROADCAST + Protocol.DELIMITER); 
            } else if (input.startsWith("pm ")) {
            	// whisper includes a user and a text. But these are already in the good format.
            	if (input.length() - input.replace(";", "").length() == 1) {
            		input = input.replaceFirst("pm ", Protocol.WHISPER + Protocol.DELIMITER);
            	} else {
            		printLine("You have too much ';' characters in your command. (max. 1)");
            		input = null;
            	}
            } else if (input.startsWith("game ")) {
            	input = input.replaceFirst("game ", Protocol.GAMECHAT + Protocol.DELIMITER); 
            } else if (input.equals("chatusers")) {
            	input = Protocol.CHATUSERS;
            }
        	
        	
            else if (input.equals("help")) {
            	printHelp();
            	input = null;
            }
        	
        
    	} else { // if the user may not use this command right now:
    		printLine("You cannot use command (" + input + ") right now! Available commands:");
    		for (String c : availableCommands) {
    			printLine(c);
    		}
    		printLine("\n\n Type 'help' for more info.");
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
    
    public void printHelp() {
    	printLine(COMMANDS);
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
