package connectfour;

import java.util.Timer;
import java.util.TimerTask;

public class Game extends Thread {
	
	private Board board;
	private Player[] players;
	private int currentPlayerIndex;
	private Timer timer;
	
	public Game(Player[] players, int dim) {
		this.board = new Board(dim);
		this.players = players;
		currentPlayerIndex = 0;
	}

	public Player currentPlayer() {
		return players[currentPlayerIndex];
	}
	
	public Player[] getPlayers() {
		return players;
	}
		
	private void reset() {
		currentPlayerIndex = 0;
		board.reset();
	}

	@Override
	public void run() {
		while (!board.gameOver()) {
			for (Player player: players) {
				player.makeMove(currentPlayer(), board);
			}
			currentPlayerIndex = (currentPlayerIndex + 1) % 2;
		}
	}
	
	public void setTimeout() {
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				ClientHandler handler = ((HumanPlayer) p).getHandler();
				timer.schedule(new TimerTask() {
					public void run() {
						handler.writeOutput(Protocol.ERROR_USERQUIT + Protocol.DELIMITER + currentPlayer().getName());
					}
				}, 20 * 1000);
			}
		}	
	}
}
