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
import cf.game.Player;
import cf.game.Protocol;

public class ClientTui implements Runnable {
	private BufferedWriter out;
	private Socket sock;
	public boolean usernameSet = false;
	public String username;
	public Set<String> availableCommands = new HashSet<>();
	public int dimension = Protocol.DIM; // default dimension
	private Board boardTui; // a copy of the board in Client to calculate fallen pieces.
	 
    /*@
    	requires sock != null
     */
    /**
     * Constructor for a new ClientTui
     */
	public ClientTui(Socket sock) {
    	try {
			// in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	this.sock = sock;
    	
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
		System.out.print("Hi there! Please enter your username: ");
		//TODO: make hello command automated: check if chat/leaderboard/... is enabled and apply that to the HELLO method
		String input = "";
    	while (input == null || !input.equals("exit")) {
			input = readString();
			try {
				if (!usernameSet) {
					out.write("HELLO;" + input);
					out.newLine();
					out.flush();
					username = input;
				} else if (!input.equals("exit")) {
					input = reformInput(input);
					if (input != null) {
						out.write(input);
						out.newLine();
						out.flush();
						System.out.println("Command has been send (" + input + ")");
					}
				}
			} catch (IOException e) {
				System.out.println("ERROR: Socket is closed!");
			}
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
            	s.close();
            } else if (input.equals("play human")) {
            	input = "PLAY" +Protocol.DELIMITER+ "HUMAN" +Protocol.DELIMITER;
            } else if (input.startsWith("play computer ")) {            	
            	Scanner s = new Scanner(input);
            	s.next(); // skip the text. Go to the int.
            	s.next();
            	int d = s.nextInt();
            	input = "PLAY" +Protocol.DELIMITER+ "COMPUTER" +Protocol.DELIMITER +d;            	
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
            }
    	} else {
    		System.out.println("You cannot use command (" + input + ") right now! Available commands: ");
    		for (String c : availableCommands) {
    			System.out.println(c);
    		}
    		input = null;
    	}
    
    	return input;
	}


	/**
     * Closes the connection, the sockets will be terminated.
     */
    public void shutDown() {
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
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
        }

        return (antw == null) ? "" : antw;
    }   
    
}
