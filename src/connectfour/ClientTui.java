package connectfour;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Scanner;

public class ClientTui implements Runnable {
	BufferedReader in;
	BufferedWriter out;
	Socket sock;
	
	
	 
    /*@
    	requires sock != null
     */
    /**
     * Constructor for a new ClientTui
     */
	public ClientTui(Socket sock) {
    	try {
			in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	this.sock = sock;
    	
	}

	
	@Override
	public void run() {
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
     * Reads a string from the console and sends this string over
     * the socket-connection to the ClientTui process.
     * On "exit" the method ends
     */
    public void handleTerminalInput() {
		String input = "";
    	while (!input.equals("exit")) {
			input = readString();
			try {
				if (!input.equals("exit")) {
					out.write(input);
					out.newLine();
					out.flush();
					System.out.println("Command has been send (" + input + ")");
				}
			} catch (IOException e) {
				System.out.println("ERR: Socket is closed!");
			}
		}
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
    
    
    /**
     * Method for processing input from the server.
     * 
     * @param input The input message from the server.
     */
    private void processInput(String input) {
    	Scanner scanner = new Scanner(input);
    	String command = scanner.next();
    	System.out.println(input);
    	//TODO: Add methods or functions
    	switch (command) {
    		
    		// Connect to a server:
    		case "HELLO":
    			//do this
    			break;
    		case "ERR_USERNAME_TAKEN":
    			//do this
    			break;
    		
    		// Starting a game
    		case "WAIT":
    			//do this
    			break;
    		case "READY":
    			//do this
    			break;
    		
    		// Playing a game
    		case "REQUESTMOVE":
    			//do this
    			break;
    		case "SETMOVE":
    			//do this
    			break;
    		case "ERR_INVALIDMOVE":
    			//do this
    			break;
    		case "ERR_NOTYOURTURN":
    			//do this
    			break;
    		case "GAMEOVER":
    			//do this
    			break;
    		case "ERR_USERQUIT":
    			//do this
    			break;
    		
    			
    		// ====== OPTIONALS ======
    		// Chat
    		case "BROADCAST":
    			//do this
    			break;
    		case "WHISPER":
    			//do this
    			break;
    		case "CHATUSERS":
    			//do this
    			break;
    		case "GAMECHAT":
    			//do this
    			break;
    		case "ERR_ISERNOTFOUNDCHAT":
    			//do this
    			break;
    		case "ERR_USERHASNOCHAT":
    			//do this
    			break;
    		case "ERR_NOTINAGAME":
    			//do this
    			break;
    		
    		// Challenge
    		
    		// Leaderboard
    			
    		// Password
    		
    		// Other
    		case "ERR_COMMANDNOTRECOGNIZED":
    			//do this
    			break;
    	}
    }
    
    
}
