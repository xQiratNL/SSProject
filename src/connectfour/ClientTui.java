package connectfour;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

public class ClientTui implements Runnable {
	// BufferedReader in;
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
			// in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	this.sock = sock;
    	
	}


	/**
     * Reads a string from the console and sends this string over
     * the socket-connection to the ClientTui process.
     * On "exit" the method ends
     */
	@Override
	public void run() {
		String input = "";
    	while (!input.equals("exit")) {
			input = readString();
			try {
				input = reformInput(input);
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
     * Changes input given by the user in the TUI to a readable command for the server.
     * 
     * @param input input to handle.
     * @return
     */
    private String reformInput(String input) {        
        if (input.startsWith("hello ")) {
        	input = input.replaceFirst("hello ", "HELLO;");
        	//TODO: make hello command automated: check if chat/leaderboard/... is enabled and apply that to the HELLO mehtod
        } else if (input.startsWith("play human ")) {
        	input = input.replaceFirst("play human ", "PLAY;HUMAN;");
        } else if (input.equals("play human")) {
        	input = "PLAY;HUMAN;";
        } else if (input.startsWith("play computer ")) {
        	input = input.replaceFirst("play computer ", "PLAY;COMPUTER;");
        } else if (input.equals("play computer")) {
        	input = "PLAY;COMPUTER;";
        } else if (input.startsWith("make move ")) {
        	input = input.replaceFirst("make move ", "MAKEMOVE;");
        } else if (input.startsWith("ready")) {
        	input = input.replaceFirst("ready", "READY");
        } else if (input.startsWith("decline")) {
        	input = input.replaceFirst("decline", "DECLINE");
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
