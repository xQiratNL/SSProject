package cf.server;

import java.util.Scanner;

import cf.Protocol;

public class ServerTui {

	public void println(String msg) {
		System.out.println(msg);
	}
	
	public int askServerNumber() {
		int portnumber = Protocol.PORTNUMBER;
		@SuppressWarnings("resource") // you don't want to close system.in since it can't be opened again.
		Scanner in = new Scanner(System.in);
		boolean correctInput = false;
		do {
			System.out.print("Enter port number (default " + Protocol.PORTNUMBER + "):");
			String input = in.nextLine();
			try {
				correctInput = true;
				if (!input.isEmpty()) {
					portnumber = Integer.parseInt(input);
				}
			} catch (NumberFormatException e) {
				println("Please enter a valid portnumber.");
				correctInput = false;
			}
		} while (!correctInput);
		return portnumber;
	}
}
