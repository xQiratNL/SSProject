package connectfour;

import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.io.IOException;

public class Server {
	
	private ServerTui tui;
	private List<String> usernames = new ArrayList<String>();
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
				new Thread(new ClientHandler(this, sock, tui)).start();;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void addUsername(String username) {
		usernames.add(username);
	}
	
	public List<String> getUsernames() {
		return usernames;
	}
	
	public static void main (String[] args) {
		new Server();
	}
}
