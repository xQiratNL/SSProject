package cf.server;

import java.net.Socket;

import cf.game.Mark;
import cf.Protocol;

import java.io.IOException;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class ClientHandler extends Thread {
	
	private Server server;
	private Socket sock; //socket of client
	private ServerTui tui; //tui of server
	private BufferedReader in; //inputstream of client
	private BufferedWriter out; //outputstream of client
	private String username = "";
	private Game game;
	public enum ClientStatus {CONNECTED, IN_LOBBY, IN_WAIT, IN_READY, IN_GAME}; //status of this client, used in determining which commands are possible.
	private ClientStatus status = ClientStatus.CONNECTED;

	
	/**
	 * Create a clienthandler, which deals with all input and output of a single client and writes all communication on the server's tui
	 * @param server The server.
	 * @param sock, the socket of the client.
	 * @param tui, the tui of the server.
	 */
	public ClientHandler(Server server, Socket sock, ServerTui tui) {
		this.server = server;
		this.sock = sock;
		this.tui = tui;
	}

	
	@Override
	/**
	 * Gets the in and outputstream of the client socket and sends all input from the client to the method processInput.
	 */
	public void run() {
		try {
			this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {
			tui.printException(e);
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
	
	/**
	 * Writes output to the client and also prints communication to the server's tui.
	 * @param output, output to send to client
	 */
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
	
	/**
	 * Calls function on given input, or tells client that the command is unknown (at this time).
	 * Also print user input on server's tui.
	 * @param input, input to process.
	 */
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
					try {
						play(splitInput);
						break;
					} catch (NumberFormatException e){
						//no break so goes to default
					}
				} //else command entered at wrong time
			case Protocol.READY:
				if (status == ClientStatus.IN_READY) {
					ready();
					break;
				} //else command entered at wrong time
			case Protocol.DECLINE:
				if (status == ClientStatus.IN_READY) {
					decline();
					break;
				} else if (status == ClientStatus.IN_WAIT){
					declineWait();
				} //else command entered at wrong time
			case Protocol.MAKEMOVE:
				if (status == ClientStatus.IN_GAME) {
					makeMove(splitInput);
					break;
				} //else command entered at wrong time
			default:
				//wrong command given or given at wrong time
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	/**
	 * Process the command hello ...
	 * @param input command of user
	 */
	public void hello(String[] input) {
		if (input.length == 2) {
			if (server.nameTaken(input[1])) {//usernametaken
				writeOutput(Protocol.ERROR_USERNAMETAKEN);
			} else {//command correct
				username = input[1];
				server.addUser(this);
				writeOutput(Protocol.HELLO + Protocol.DELIMITER + Server.EXT);
				status = ClientStatus.IN_LOBBY;
			}
		} else { //invalid input
			writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	/**
	 * Process the command play...
	 * @param input command of user
	 */
	public void play(String[] input) throws NumberFormatException {
		if (input.length == 2 || input.length == 3) {
			int dim = Protocol.DIM;
			if (input.length == 3) {//Set dim to default if no dim given.
					dim = Integer.parseInt(input[2]);
			}
			if (input[1].equals(Protocol.HUMAN)) {//play against human
				ClientHandler opponent = server.popFirstWaitingUser(dim);
				if (null == opponent) {//no opponent found
					server.addWaitingUser(dim, this);
					writeOutput(Protocol.WAIT);
					status = ClientStatus.IN_WAIT;
				} else {//opponent found
					game = newGame(opponent, dim);
					opponent.setGame(game);
					String msg = Protocol.READY + Protocol.DELIMITER + username + Protocol.DELIMITER + opponent.getUsername();
					writeOutput(msg);
					opponent.writeOutput(msg);//inform opponent
					status = ClientStatus.IN_READY;
					opponent.setStatus(ClientStatus.IN_READY);//change opponents state
					game.setFirstTimeout();
				}			
			} else if (input[1].equals(Protocol.COMPUTER)) {//play against copmuter
				game = newGame(dim);
				//get name and send it to client
				String computername = "";
				for (Player p : game.getPlayers()) {
					if (p instanceof ComputerPlayer) {
						computername = p.getName();
					}
				}
				String msg = Protocol.READY + Protocol.DELIMITER + username + Protocol.DELIMITER + computername;
				writeOutput(msg);
				status = ClientStatus.IN_READY;
				game.setFirstTimeout();
			} else {// wrong command not human/computer
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
			}
		} else { //invalid command
			tui.println(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	/**
	 * user says ready start game if not already started.
	 */
	public void ready() {
		status = ClientStatus.IN_GAME;
		if (!game.isAlive()) {
			game.start();
		}
	}
	
	/**
	 * user declines the game, tell other user that client quit
	 */
	public void decline() {
		game.cancelTimer();
		for (Player p: game.getPlayers()) {
			if (p instanceof HumanPlayer && ((HumanPlayer) p).getHandler() != this) {
				((HumanPlayer) p).getHandler().writeOutput(Protocol.ERROR_USERQUIT + Protocol.DELIMITER + this.username);
			}
		}
	}
	
	/**
	 * Users declines while waiting, returns to lobby and gets removed from waiting list on server.
	 */
	public void declineWait() {
		server.removeWaiting(this);
		status = ClientStatus.IN_LOBBY;
	}
	
	/**
	 * Users makes move
	 * @param input user command makemove x y z
	 */
	public void makeMove(String[] input) {
		if (((HumanPlayer) game.currentPlayer()).getHandler() == this) {
			if (input.length == 4) {
				try {
					int x = Integer.parseInt(input[1]);
					int y = Integer.parseInt(input[2]);
					int z = Integer.parseInt(input[3]);
					game.makeMove(username, x, y, z);
				} catch (NumberFormatException e) {//users sends incorrect x/y/z value
					writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
				}
			} else {//user sends incorrect command
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
			}
		} else {//user tries to make move while not its turn
			writeOutput(Protocol.ERROR_NOTYOURTURN);
		}
	}

	/**
	 * Create a newgame against computerplayer 50% chance on X or y
	 * @param dim dimension of board
	 * @return game object
	 */
	public Game newGame(int dim) {
		Mark mark = Mark.XX;
		if (Math.random() >= 0.5) {//50% chance on O/X
			mark = Mark.OO;
		}
		HumanPlayer playerOne = new HumanPlayer(this, mark);
		ComputerPlayer playerTwo = new ComputerPlayer(mark.other());
		return new Game(new Player[] {playerOne, playerTwo}, dim);
	}
	
	/**
	 * Create a newgame against other humanplayer 50% chance on X or y
	 * @param opponent other player (clienthandler)
	 * @param dim dimension of board
	 * @return game object
	 */
	public Game newGame(ClientHandler opponent, int dim) {
		Mark mark = Mark.XX;
		if (Math.random() >= 0.5) {//50% chance on O/X
			mark = Mark.OO;
		}
		HumanPlayer playerOne = new HumanPlayer(this, mark);
		HumanPlayer playerTwo = new HumanPlayer(opponent, mark.other());
		return new Game(new Player[] {playerOne, playerTwo}, dim);
	}
	
	/**
	 * Set game of client
	 * @param game, game object to pass
	 */
	public void setGame(Game game) {
		this.game = game;
	}
	
	/**
	 * @return Username of client
	 */
	public String getUsername() {
		return username;
	}
	
	/**
	 * Change a clients status
	 * @param newStatus, client (ClientStatus) to change it to.
	 */
	public void setStatus(ClientStatus newStatus) {
		status = newStatus;
	}
	
	/**
	 * Get status of client
	 * @return status (ClienStatus) of client
	 */
	public ClientStatus getStatus() {
		return status;
	}
	
	/**
	 * @return true if socket closed.
	 */
	public boolean isClosed() {
		return sock.isClosed();
	}
}
