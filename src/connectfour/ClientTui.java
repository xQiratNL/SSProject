package connectfour;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.HashSet;
import java.util.Set;

public class ClientTui implements Runnable {
	private BufferedWriter out;
	private Socket sock;
	public boolean usernameSet = false;
	public String username;
	public Set<String> availableCommands = new HashSet<>();
	public int dimension = Protocol.DIM; // default dimension
	 
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
			// cut the command to the first 4 letters. This causes easily command handling and checking.
			c.substring(0, Math.min(c.length(), 4));
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
	public boolean removeCommands(String... command) {
		boolean correct = true;
		for (String c: command) {
			// cut the command to the first 4 letters. This causes easily command handling and checking.
			c.substring(0, Math.min(c.length(), 4));
			correct = availableCommands.add(c);
		}
		return correct;
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
    	if (availableCommands.contains(input.substring(0, Math.min(input.length(), 4)))) {
    		// command is available at this moment!
        	if (input.startsWith("play human ")) {
            	input = input.replaceFirst("play human ", "PLAY" +Protocol.DELIMITER+ "HUMAN" +Protocol.DELIMITER);
            	try {
            		dimension = Integer.parseInt(input);
            	} catch (NumberFormatException e) {
            		// no dimension given.
            		// so, do nothing
            	}
            } else if (input.equals("play human")) {
            	input = "PLAY" +Protocol.DELIMITER+ "HUMAN" +Protocol.DELIMITER;
            } else if (input.startsWith("play computer ")) {
            	input = input.replaceFirst("play computer ", "PLAY" +Protocol.DELIMITER+ "COMPUTER" +Protocol.DELIMITER);
            	try {
            		dimension = Integer.parseInt(input);
            	} catch (NumberFormatException e) {
            		// no dimension given.
            		// so, do nothing
            	}
            } else if (input.equals("play computer")) {
            	input = "PLAY" +Protocol.DELIMITER+ "COMPUTER" +Protocol.DELIMITER;
            } else if (input.startsWith("move ")) {
            	try {
                	Board b = new Board(dimension);
                	int[] coords = b.coordinates(Integer.parseInt(input));
                	input = input.replaceFirst("move ", "MAKEMOVE" +Protocol.DELIMITER + coords[0] + Protocol.DELIMITER + coords[1] + Protocol.DELIMITER + coords[2]);
            	} catch (NumberFormatException e) {
            		// no number given or something went wrong. Try again...
            		System.out.println("Something went wrong. Maybe you can't make that move? Try again!");
            	}

            } else if (input.startsWith("ready")) {
            	input = input.replaceFirst("ready", "READY");
            } else if (input.startsWith("decline")) {
            	input = input.replaceFirst("decline", "DECLINE");
            }
    	} else {
    		input = null;
    		System.out.println("You cannot use this command right now!");
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
