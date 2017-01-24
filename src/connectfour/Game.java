package connectfour;

import java.util.Timer;
import java.util.TimerTask;

public class Game extends Thread {
	
	private Board board;
	private Player[] players;
	private int currentPlayerIndex;
	private Timer timer = new Timer();
	private boolean moveMade = false;
	
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
	
	private void makeMove(Player player, int field) {
		board.setField(field, player.getMark());
	}
	
	public void makeMove(String username, int x, int y, int z) {
		timer.purge();
		for (Player p: players) {
			if (p.getName().equals(username)) {
				if (board.isValidMove(x, y, z)) {
					board.setField(x, y, z, p.getMark());
				} else {
					((HumanPlayer) p).getHandler().writeOutput(Protocol.ERROR_INVALIDMOVE);
				}
			}
		}
		moveMade = true;
	}

	
	@Override
	public void run() {
		timer.purge();
		while (!board.gameOver()) {
			if (currentPlayer() instanceof ComputerPlayer) {
				makeMove(currentPlayer(), ((ComputerPlayer) currentPlayer()).determineMove(board));
			} else {
				for (Player p: players) {
					if (p instanceof HumanPlayer) {
						((HumanPlayer) p).requestMove(currentPlayer(), board);
					}
				}
				setTimeout();
				
				//TODO: improve this
				while(!moveMade) {
					//keep waiting
				}
			}
			currentPlayerIndex = (currentPlayerIndex + 1) % 2;
		}
	}
	
	public void moveMade() {
		moveMade = true;
	}
	
	public void setFirstTimeout() {
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				ClientHandler handler = ((HumanPlayer) p).getHandler();
				timer.schedule(new TimerTask() {
					public void run() {
						//TODO: maybe change this
						handler.writeOutput(Protocol.GAMEOVER);
					}
				}, 20 * 1000);
			}
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
