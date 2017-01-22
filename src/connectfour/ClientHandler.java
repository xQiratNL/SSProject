package connectfour;

import java.net.Socket;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class ClientHandler implements Runnable {
	
	private Server server;
	private Socket sock;
	private ServerTui tui;
	private BufferedReader in;
	private BufferedWriter out;
	private String username = "";

	public ClientHandler(Server server, Socket sock, ServerTui tui) {
		this.server = server;
		this.sock = sock;
		this.tui = tui;
	}

	@Override
	public void run() {
		try {
			this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
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
	
	public void writeOutput(String output) {
		tui.println("Server replies to user " + username + " :" + output);
		try {
			out.write(output);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void processInput(String input) {
		tui.println("User " + username +" says:"  + input);
		// TODO Wrong input commands (maybe)
		String[] splitInput = input.split(Protocol.DELIMITER);
		switch (splitInput[0]) {
			case Protocol.HELLO:
				hello(splitInput);
				break;
			case Protocol.PLAY:
				play(splitInput);
				break;
			case Protocol.READY:
				ready();
				break;
			case Protocol.DECLINE:
				decline();
				break;
			case Protocol.MAKEMOVE:
				makeMove(splitInput);
				break;
			default:
				//wrong command given
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	public void hello(String[] input) {
		//TODO No username given (maybe)
		if (server.getUsernames().contains(input[1])) {
			writeOutput(Protocol.ERROR_USERNAMETAKEN);
		} else {
			username = input[1];
			server.addUsername(username);
			writeOutput(Protocol.HELLO + Protocol.DELIMITER + Server.EXT);
		}
	}
	
	public void play(String[] input) {
		
	}
	
	public void ready() {
		
	}
	
	public void decline() {
		
	}
	
	public void makeMove(String[] input) {
		
	}
}
