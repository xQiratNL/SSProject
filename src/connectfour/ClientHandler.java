package connectfour;

import java.net.Socket;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class ClientHandler extends Thread {
	
	private Server server;
	private Socket sock;
	private ServerTui tui;
	private BufferedReader in;
	private BufferedWriter out;
	private String username = "";
	private Game game;

	public ClientHandler(Server server, Socket sock, ServerTui tui) {
		this.server = server;
		this.sock = sock;
		this.tui = tui;
	}

	//TODO check concurrency
	
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
	
	public synchronized void writeOutput(String output) {
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
		if (server.getUsers().values().contains(input[1])) {
			writeOutput(Protocol.ERROR_USERNAMETAKEN);
		} else {
			username = input[1];
			server.addUser(this, username);
			writeOutput(Protocol.HELLO + Protocol.DELIMITER + Server.EXT);
		}
	}
	
	public void play(String[] input) {
		//TODO: no second argument (maybe) or wrong third
		int dim = Protocol.DIM;
		if (input.length == 3) {
			dim = Integer.parseInt(input[2]);
		}
		if (input[1] == Protocol.HUMAN) {
			ClientHandler opponent = server.popFirstWaitingUser(dim);
			if (opponent.equals(null)) {
				writeOutput(Protocol.WAIT);
			} else {
				game = newGame(opponent, dim);
				opponent.setGame(game);
				String msg = Protocol.READY + Protocol.DELIMITER + username + Protocol.DELIMITER + opponent.getUsername() + Protocol.DELIMITER;
				writeOutput(msg);
				opponent.writeOutput(msg);
			}			
		} else if (input[1] == Protocol.COMPUTER) {
			game = newGame(dim);
			String msg = Protocol.READY + Protocol.DELIMITER + username + Protocol.DELIMITER + "ComputerPlayer" + Protocol.DELIMITER;
			writeOutput(msg);
		} else {
			writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	//TODO: 20 second time-out 
	
	public void ready() {
		//TODO: implement
	}
	
	public void decline() {
		//TODO: implement
	}
	
	public void makeMove(String[] input) {
		//TODO: implement
	}
	
	
	//TODO: random X/O (maybe)
	public Game newGame(int dim) {
		HumanPlayer playerOne = new HumanPlayer(this.username, Mark.XX);
		ComputerPlayer playerTwo = new ComputerPlayer(Mark.OO);
		return new Game(new Player[] {playerOne, playerTwo}, dim);
	}
	
	//TODO: random X/O (maybe)
	public Game newGame(ClientHandler opponent, int dim) {
		HumanPlayer playerOne = new HumanPlayer(this.username, Mark.XX);
		HumanPlayer playerTwo = new HumanPlayer(opponent.getUsername(), Mark.OO);
		return new Game(new Player[] {playerOne, playerTwo}, dim);
	}
	
	public void setGame(Game game) {
		this.game = game;
	}
	
	public String getUsername() {
		return username;
	}
}
