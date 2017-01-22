package connectfour;

import java.net.ServerSocket;
import java.net.Socket;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.io.IOException;

public class Server {
	
	private ServerTui tui;
	private Map<ClientHandler, String> users = new HashMap<ClientHandler, String>();
	private Map<Integer, List<ClientHandler>> waitingUsers = new HashMap<Integer, List<ClientHandler>>();
	public static final String EXT = ""; //change when optionals implemented
	
	public Server() {
		tui = new ServerTui();
		this.start();
	}

	public void start() {
		try (ServerSocket ssock = new ServerSocket(Protocol.PORTNUMBER);) {
			tui.println("Server has started on port: " + ssock.getLocalPort());
			int i = 0;
			while (true) {
				Socket sock = ssock.accept();
				tui.println("New client " + ++i +  " has connected");
				new ClientHandler(this, sock, tui).start();
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public synchronized void addUser(ClientHandler handler, String username) {
		users.put(handler, username);
	}
	
	public synchronized Map<ClientHandler, String> getUsers() {
		return users;
	}
	
	public synchronized void addWaitingUser(int dim, ClientHandler handler) {
		if (!waitingUsers.containsKey(dim)) {
			waitingUsers.put(dim, new ArrayList<>());
		}
		waitingUsers.get(dim).add(handler);
	}
	
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
	
	public static void main (String[] args) {
		new Server();
	}
}
