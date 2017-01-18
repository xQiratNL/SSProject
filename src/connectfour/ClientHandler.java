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
	
	public void processInput(String input) {
		tui.println(input);
	}
}
