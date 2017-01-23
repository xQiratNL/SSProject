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
		tui.println("Server replies to user " + username + ": " + output);
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
				game.setFirstTimeout();
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
		if (input[1].equals(Protocol.HUMAN)) {
			ClientHandler opponent = server.popFirstWaitingUser(dim);
			if (opponent.equals(null)) {
				writeOutput(Protocol.WAIT);
			} else {
				game = newGame(opponent, dim);
				opponent.setGame(game);
				String msg = Protocol.READY + Protocol.DELIMITER + username + Protocol.DELIMITER + opponent.getUsername();
				writeOutput(msg);
				opponent.writeOutput(msg);
			}			
		} else if (input[1].equals(Protocol.COMPUTER)) {
			game = newGame(dim);
			String computername = "computerplayer";
			for (Player p : game.getPlayers()) {
				if (p instanceof ComputerPlayer) {
					computername = p.getName();
				}
			}
			String msg = Protocol.READY + Protocol.DELIMITER + username + Protocol.DELIMITER + computername;
			writeOutput(msg);
		} else {
			writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	public void ready() {
		game.start();
	}
	
	public void decline() {
		for (Player p: game.getPlayers()) {
			if (p instanceof HumanPlayer && ((HumanPlayer) p).getHandler() == this) {
				((HumanPlayer) p).getHandler().writeOutput(Protocol.ERROR_USERQUIT + Protocol.DELIMITER + this.username);
			}
		}
	}
	
	public void makeMove(String[] input) {
		//TODO: input by wrong user, or wrong input, check valid move
		if (input.length == 4) {
			int x = Integer.parseInt(input[1]);
			int y = Integer.parseInt(input[2]);
			int z = Integer.parseInt(input[3]);
			game.makeMove(username, x, y, z);
		} else {
			writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	
	//TODO: random X/O (maybe)
	public Game newGame(int dim) {
		HumanPlayer playerOne = new HumanPlayer(this, Mark.XX);
		ComputerPlayer playerTwo = new ComputerPlayer(Mark.OO);
		return new Game(new Player[] {playerOne, playerTwo}, dim);
	}
	
	//TODO: random X/O (maybe)
	public Game newGame(ClientHandler opponent, int dim) {
		HumanPlayer playerOne = new HumanPlayer(this, Mark.XX);
		HumanPlayer playerTwo = new HumanPlayer(opponent, Mark.OO);
		return new Game(new Player[] {playerOne, playerTwo}, dim);
	}
	
	public void setGame(Game game) {
		this.game = game;
	}
	
	public String getUsername() {
		return username;
	}
}
