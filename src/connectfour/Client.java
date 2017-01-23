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
    	ClientTui tui = new ClientTui(sock);
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
    	String command = scanner.next();
    	System.out.println(input);
    	switch (command) {
    		
    		// Connect to a server:
    		case Protocol.HELLO:
    			//do this
    			break;
    		case Protocol.ERROR_USERNAMETAKEN:
    			//do this
    			break;
    		
    		// Starting a game
    		case Protocol.WAIT:
    			//do this
    			break;
    		case Protocol.READY:
    			//do this
    			break;
    		
    		// Playing a game
    		case Protocol.REQUESTMOVE:
    			//do this
    			break;
    		case Protocol.SETMOVE:
    			//do this
    			break;
    		case Protocol.ERROR_INVALIDMOVE:
    			//do this
    			break;
    		case Protocol.ERROR_NOTYOURTURN:
    			//do this
    			break;
    		case Protocol.GAMEOVER:
    			//do this
    			break;
    		case Protocol.ERROR_USERQUIT:
    			//do this
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
    			System.out.println("Command not recognized!");
    			//TODO: make usage function
    			break;
    	}
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
