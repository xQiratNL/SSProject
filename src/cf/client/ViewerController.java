package cf.client;

import java.util.HashSet;
import java.util.Set;

import cf.game.Board;

public class ViewerController {

	private Board b;
	
	public void updateBoard(Board b) {
		this.b = b;
		
		// Reads the board and all it's marks.
		// Make a new view with all the set marks.
		
		Set<int[]> marks = new HashSet<>();
		
		Viewer view = new Viewer();
		Thread t = new Thread(view);
	}
	
}
