package connectfour;

import java.util.Scanner;

public class ServerTui {

	public void println(String msg) {
		System.out.println(msg);
	}
	
	public int askServerNumber() {
		int portnumber = Protocol.PORTNUMBER;
		//TODO: close scanner
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
