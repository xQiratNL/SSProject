package cf.server;

import java.net.Socket;

import cf.game.ComputerPlayer;
import cf.game.Game;
import cf.game.HumanPlayer;
import cf.game.Mark;
import cf.game.Player;
import cf.game.Protocol;

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
	public enum ClientStatus {CONNECTED, IN_LOBBY, IN_WAIT, IN_READY, IN_GAME};
	private ClientStatus status = ClientStatus.CONNECTED;

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
			tui.println(e.getMessage());
		}
		
		while (!sock.isClosed()) {
    		try {
				if (in.ready()) {
					processInput(in.readLine());
				}
			} catch (IOException e) {
				tui.println(e.getMessage());
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
			tui.println(e.getMessage());
		}
	}
	
	public void processInput(String input) {
		tui.println("User " + username +" says: "  + input);
		String[] splitInput = input.split(Protocol.DELIMITER);
		switch (splitInput[0]) {
			case Protocol.HELLO:
				if (status == ClientStatus.CONNECTED) {
					hello(splitInput);
					break;
				} //else command entered at wrong time
			case Protocol.PLAY:
				if (status == ClientStatus.IN_LOBBY) {
					play(splitInput);
					break;
				}
			case Protocol.READY:
				if (status == ClientStatus.IN_READY) {
					ready();
					break;
				}
			case Protocol.DECLINE:
				//TODO: in wait
				if (status == ClientStatus.IN_WAIT) {
					decline();
					break;
				}
			case Protocol.MAKEMOVE:
				if (status == ClientStatus.IN_GAME) {
					makeMove(splitInput);
					break;
				}
			default:
				//wrong command given
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	public void hello(String[] input) {
		if (input.length == 2) {
			if (server.getUsers().values().contains(input[1])) {
				writeOutput(Protocol.ERROR_USERNAMETAKEN);
			} else {
				username = input[1];
				server.addUser(this, username);
				writeOutput(Protocol.HELLO + Protocol.DELIMITER + Server.EXT);
				status = ClientStatus.IN_LOBBY;
			}
		} else {
			writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	public void play(String[] input) {
		if (input.length == 2 || input.length == 3) {
			int dim = Protocol.DIM;
			if (input.length == 3) {
				dim = Integer.parseInt(input[2]);
			}
			if (input[1].equals(Protocol.HUMAN)) {
				ClientHandler opponent = server.popFirstWaitingUser(dim);
				if (null == opponent) {
					server.addWaitingUser(dim, this);
					writeOutput(Protocol.WAIT);
					status = ClientStatus.IN_WAIT;
				} else {
					game = newGame(opponent, dim);
					opponent.setGame(game);
					String msg = Protocol.READY + Protocol.DELIMITER + username + Protocol.DELIMITER + opponent.getUsername();
					writeOutput(msg);
					opponent.writeOutput(msg);
					status = ClientStatus.IN_READY;
					opponent.setStatus(ClientStatus.IN_READY);
					game.setFirstTimeout();
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
				status = ClientStatus.IN_READY;
				game.setFirstTimeout();
			} else {
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
			}
		} else {
			tui.println(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	public void ready() {
		status = ClientStatus.IN_GAME;
		if (!game.isAlive()) {
			game.start();
		}
	}
	
	public void decline() {
		for (Player p: game.getPlayers()) {
			if (p instanceof HumanPlayer && ((HumanPlayer) p).getHandler() == this) {
				((HumanPlayer) p).getHandler().writeOutput(Protocol.ERROR_USERQUIT + Protocol.DELIMITER + this.username);
			}
		}
	}
	
	public void makeMove(String[] input) {
		if (((HumanPlayer) game.currentPlayer()).getHandler() == this) {
			if (input.length == 4) {
				try {
					int x = Integer.parseInt(input[1]);
					int y = Integer.parseInt(input[2]);
					int z = Integer.parseInt(input[3]);
					game.makeMove(username, x, y, z);
				} catch (NumberFormatException e) {
					writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
				}
			} else {
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
			}
		} else {
			writeOutput(Protocol.ERROR_NOTYOURTURN);
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
	
	public void setStatus(ClientStatus newStatus) {
		status = newStatus;
	}
	
	public ClientStatus getStatus() {
		return status;
	}
}
