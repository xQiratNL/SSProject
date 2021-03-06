package cf.server;

import java.net.ServerSocket;
import java.net.Socket;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

import cf.Protocol;

import java.util.ArrayList;
import java.io.IOException;

public class Server {
	
	private ServerTui tui; //tui of the server
	private ConcurrentMap<ClientHandler, String> users = new ConcurrentHashMap<ClientHandler, String>(); //users logged on to the server
	private ConcurrentMap<Integer, List<ClientHandler>> waitingUsers = new ConcurrentHashMap<Integer, List<ClientHandler>>(); //users waiting on a game
	public static final String EXT = Protocol.EXT_CHAT; //implemented optionals
	
	/**
	 * Constructs a new server, with a tui and calls the method start on this server.
	 */
	public Server() {
		tui = new ServerTui();
		this.start();
	}

	/**
	 * This method creates asks the user for a portnumber via the tui and creates a serversocket.
	 * After that it waits for incoming connections and if so it creates a handler thread which will 
	 * deal with all clientrelated matter.
	 */
	public void start() {
		while (true) {
			try (ServerSocket ssock = new ServerSocket(tui.askPortNumber());) {
				tui.println("Server has started on port: " + ssock.getLocalPort());
				int i = 0;
				while (true) {
					Socket sock = ssock.accept();
					tui.println("New client " + ++i +  " has connected");
					new ClientHandler(this, sock, tui).start();
				}
			} catch (IOException e) {
				tui.printException(e);
			}
		}
	}
	
	/**
	 * Adds a handler with corresponding name to the users in the server.
	 * @param handler handler which should be added.
	 */
	public synchronized void addUser(ClientHandler handler) {
		users.put(handler, handler.getUsername());
	}
	/**
	 * Checks if username is taken. If name taken but connection closed, then name is made free.
	 * @param name,name to check.
	 * @return true if username free.
	 */
	public synchronized boolean nameTaken(String name) {
		return users.containsValue(name);
	}
	
	/**
	 * Adds a user to the list of users that are waiting for a game of a given dimension.
	 * @param dim, dimension of the game, the client wants to play.
	 * @param handler, ClientHandler of the client.
	 */
	public synchronized void addWaitingUser(int dim, ClientHandler handler) {
		if (!waitingUsers.containsKey(dim)) {
			waitingUsers.put(dim, new ArrayList<ClientHandler>());
		}
		waitingUsers.get(dim).add(handler);
	}
	
	/**
	 * Returns the first waiting user for a game of a certain dimension.
	 * @param dim, dimension of the game to play.
	 * @return ClientHandle of the player, or null if no such player exists.
	 */
	public synchronized ClientHandler popFirstWaitingUser(int dim) {
		if (!waitingUsers.containsKey(dim)) {
			return null;
		}
		ClientHandler handler = waitingUsers.get(dim).remove(0);
		if (waitingUsers.get(dim).size() == 0) {
			waitingUsers.remove(dim);
		}
		return handler;
	}

	/**
	 * Removes given handler from the waiting list.
	 * @param handler, handler to remove
	 */
	public synchronized void removeWaiting(ClientHandler handler) {
		for (int dim: waitingUsers.keySet()) {
			waitingUsers.get(dim).remove(handler);
			if (waitingUsers.get(dim).size() == 0) {
				waitingUsers.remove(dim);
			}
		}
	}
	
	/**
	 * Returns map of clienthandlers and usernames connected to server.
	 * @return map<ClientHandler, String>
	 */
	public Map<ClientHandler, String> getUsers() {
		return users;
	}
	
	/**
	 * Starts a Server.
	 */
	public static void main (String[] args) {
		new Server();
	}
}
