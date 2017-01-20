package connectfour;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

public class Client {
    private static final String USAGE
    = "usage: java connectfour.Client <address>";

    /** Starts a Client application. */
    public static void main(String[] args) {
    	if (args.length != 1) {
    		System.out.println(USAGE);
    		System.exit(0);
    	}

    	InetAddress addr = null;
    	Socket sock = null;
    	
    	// check args[0] - the IP-adress
    	try {
    		addr = InetAddress.getByName(args[0]);
    	} catch (UnknownHostException e) {
    		System.out.println(USAGE);
    		System.out.println("ERROR: host " + args[1] + " unknown");
    		System.exit(0);
    	}

    	// try to open a Socket to the server
    	try {
    		sock = new Socket(addr, Protocol.PORTNUMBER);
    	} catch (IOException e) {
    		System.out.println("ERROR: could not create a socket on " + addr
    				+ " and port " + Protocol.PORTNUMBER);
    	}
    	
        // create ClientTui object in a new thread and start the two-way communication.
    	// The new thread is created to maintain two process at a time. The output and input.
    	ClientTui tui = new ClientTui(sock);
        Thread streamInputHandler = new Thread(tui);
        streamInputHandler.start();
        tui.handleTerminalInput();
        tui.shutDown();
    }
}
