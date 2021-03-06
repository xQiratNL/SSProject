package cf.server;

import java.net.Socket;
import java.util.Arrays;

import cf.Protocol;
import cf.model.Mark;

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
	private boolean ext_chat = false;
	public enum ClientStatus {CONNECTED, IN_LOBBY, IN_WAIT, IN_READY, IN_GAME}; //status of this client, used in determining which commands are possible.
	private ClientStatus status = ClientStatus.CONNECTED;

	
	/**
	 * Create a clienthandler, which deals with all input and output of a single client and writes all communication on the server's tui
	 * @param server The server.
	 * @param sock, the socket of the client.
	 * @param tui, the tui of the server.
	 */
	//@ requires server != null;
	//@ requires sock != null;
	//@ requires tui != null;
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
	//@ requires output != null;
	/*@ pure */public synchronized void writeOutput(String output) {
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
	//@ requires input != null;
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
					break;
				} //else command entered at wrong time
			case Protocol.MAKEMOVE:
				if (status == ClientStatus.IN_GAME) {
					makeMove(splitInput);
					break;
				} //else command entered at wrong time
			case Protocol.BROADCAST:
				if (!(status == ClientStatus.CONNECTED) && splitInput.length == 2) {
					broadcast(splitInput);
					break;
				} //else not yet username given
			case Protocol.WHISPER:
				if (!(status == ClientStatus.CONNECTED) && splitInput.length == 3) {
					whisper(splitInput);
					break;
				} //else not yet username given
			case Protocol.CHATUSERS:
				if (!(status == ClientStatus.CONNECTED)) {
					chatUsers();
					break;
				} //else not yet username given
			case Protocol.GAMECHAT:
				if (status == ClientStatus.IN_GAME) {
					if (splitInput.length == 2) {
						gameChat(splitInput);
						break;
					}// else wrong command so go to default
				} else {//currently not in a game
					writeOutput(Protocol.ERROR_NOT_IN_GAME);
					break;
				}	
			default:
				//wrong command given or given at wrong time
				writeOutput(Protocol.ERROR_COMMAND_NOT_RECOGNIZED);
		}
	}
	
	/**
	 * Sends message to all other users in the gamechat, if user tries to send message to computerplayer, computerplayer will give a nice reply.
	 * @param splitInput, split version of clients command
	 */
	//@ requires getStatus() == ClientStatus.IN_GAME;
	//@ requires splitInput.length == 2;	/*@ pure */private void gameChat(String[] splitInput) {
		for (Player player: game.getPlayers()) {
			if (player instanceof HumanPlayer) {
				((HumanPlayer) player).getHandler().writeOutput(Protocol.GAMECHAT + Protocol.DELIMITER + splitInput[1]);
			} else {//computerplayer
				writeOutput(Protocol.GAMECHAT + Protocol.DELIMITER + "I will crush you."); //supposed to be funny.
			}
		}
	}
	
	/**
	 * Sends all usernames who have chat implemented to the client.
	 */
	//@ requires getStatus() != ClientStatus.CONNECTED;
	/*@ pure*/private void chatUsers() {
		String users = Protocol.DELIMITER;
		for (ClientHandler user: server.getUsers().keySet()) {
			if (user.chatImplemented()) {
				users += user.getUsername() + Protocol.DELIMITER;
			}
		}
		writeOutput(Protocol.CHATUSERS + users);
	}

	/**
	 * Sends message to person to whisper to, or error message if necessary.
	 * @param input, split version of command by client
	 */
	//@ requires getStatus() != ClientStatus.CONNECTED;
	//@ requires input.length == 3;
	/*@ pure */private void whisper(String[] input) {
		if (server.getUsers().containsValue(input[1])) {
			for (ClientHandler user: server.getUsers().keySet()) {
				if (server.getUsers().get(user).equals(input[1])) {
					if (user.chatImplemented()) {
						user.writeOutput(Protocol.WHISPER + Protocol.DELIMITER + this.username + Protocol.DELIMITER + input[2]);
					} else {
						writeOutput(Protocol.ERROR_USER_HAS_NO_CHAT);
					}
					break;
				}
			}
		} else {
			writeOutput(Protocol.ERROR_USER_NOT_FOUND);
		}
	}

	/**
	 * Broadcasts message from this user to all users which implemented chat
	 * @param input, string of length 2 with second entry containing the message.
	 */
	//@ requires getStatus() != ClientStatus.CONNECTED;
	//@ requires input.length == 2;
	/*@ pure */private void broadcast(String[] input) {
		for (ClientHandler user: server.getUsers().keySet()) {
			if (user.chatImplemented() && user != this) {
				user.writeOutput(Protocol.BROADCAST + Protocol.DELIMITER + this.username + Protocol.DELIMITER + input[1]);
			}
		}
	}


	/**
	 * Process the command hello ..., also sets extensions if necessary using setExtensions
	 * @param input command of user
	 */
	//@ requires getStatus() == ClientStatus.CONNECTED;
	public void hello(String[] input) {
		if (input.length >= 2) {
			if (server.nameTaken(input[1])) {//usernametaken
				writeOutput(Protocol.ERROR_USERNAME_TAKEN);
			} else {//command correct
				if (input.length > 2) {
					setExtensions(Arrays.copyOfRange(input, 2, input.length));
				}
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
	 * Checks for input if it contains extensions implemented by the server.
	 * @param extensions
	 */
	//@ requires extensions.length >= 1;
	private void setExtensions(String[] extensions) {
		for (String ext: extensions) {
			if (ext.equals(Protocol.EXT_CHAT)) {
				ext_chat = true;
			}
		}	
	}


	/**
	 * Process the command play...
	 * @param input command of user
	 */
	//@ requires input != null;
	//@ requires getStatus() == ClientStatus.IN_LOBBY;
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
	//@ requires getStatus() == ClientStatus.IN_READY;
	public void ready() {
		status = ClientStatus.IN_GAME;
		if (!game.isAlive()) {
			game.start();
		}
	}
	
	/**
	 * user declines the game, tell other user that client quit
	 */
	//@ requires getStatus() == ClientStatus.IN_READY;
	//@ ensures getStatus() == ClientStatus.IN_LOBBY;
	public void decline() {
		game.cancelTimer();
		for (Player p: game.getPlayers()) {
			if (p instanceof HumanPlayer && ((HumanPlayer) p).getHandler() != this) {
				((HumanPlayer) p).getHandler().writeOutput(Protocol.ERROR_USER_QUIT + Protocol.DELIMITER + this.username);
				((HumanPlayer) p).getHandler().setStatus(ClientStatus.IN_LOBBY);
			}
		}
		status = ClientStatus.IN_LOBBY;
	}
	
	/**
	 * Users declines while waiting, returns to lobby and gets removed from waiting list on server.
	 */
	//@ requires getStatus() == ClientStatus.IN_WAIT;
	//@ ensures getStatus() == ClientStatus.IN_LOBBY;
	public void declineWait() {
		server.removeWaiting(this);
		status = ClientStatus.IN_LOBBY;
	}
	
	/**
	 * Users makes move
	 * @param input user command makemove x y z
	 */
	//@ requires getStatus() == ClientStatus.IN_GAME;
	//@ requires input != null;
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
			writeOutput(Protocol.ERROR_NOT_YOUR_TURN);
		}
	}

	/**
	 * Create a newgame against computerplayer 50% chance on X or y
	 * @param dim dimension of board
	 * @return game object
	 */
	//@ requires dim > 1;
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
	//@ requires opponent != null;
	//@ requires dim > 1;
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
	//@ requires game != null;
	public void setGame(Game game) {
		this.game = game;
	}
	
	/**
	 * @return Username of client
	 */
	/*@ pure */public String getUsername() {
		return username;
	}
	
	/**
	 * Change a clients status
	 * @param newStatus, client (ClientStatus) to change it to.
	 */
	//@ ensures getStatus() == newStatus;
	//@ requires newStatus != null;
	public void setStatus(ClientStatus newStatus) {
		status = newStatus;
	}
	
	/**
	 * Get status of client
	 * @return status (ClienStatus) of client
	 */
	/*@ pure */public ClientStatus getStatus() {
		return status;
	}
	
	/**
	 * @return true if socket closed.
	 */
	/* @ pure */public boolean isClosed() {
		return sock.isClosed();
	}
	
	/**
	 * @return true if client implemented chat functionality
	 */
	/*@ pure */public boolean chatImplemented() {
		return ext_chat;
	}
}
