package cf.game;

import java.util.Timer;
import java.util.TimerTask;

import cf.Protocol;
import cf.server.ClientHandler;

public class Game extends Thread {
	
	private Board board;
	private Player[] players;
	private int currentPlayerIndex;
	private Timer timer = new Timer();
	private boolean moveMade = false;
	
	/**
	 * Construct a new game object for given players and board of given dimension
	 * @param players, array of two players
	 * @param dim, dimension of the board
	 */
	public Game(Player[] players, int dim) {
		this.board = new Board(dim);
		this.players = players;
		currentPlayerIndex = 0;
	}

	/**
	 * @return Player that is to make a move.
	 */
	public Player currentPlayer() {
		return players[currentPlayerIndex];
	}
	
	/**
	 * @return Array of all players in game (2 players)
	 */
	public Player[] getPlayers() {
		return players;
	}
	
	/**
	 * Makemove for computerplayer on server.
	 * @param player computerplayer
	 * @param field, field to make move on.
	 */
	private synchronized void makeMove(Player player, int field) {
		board.setField(field, player.getMark());
		int[] coord = board.coordinates(field);
		informMoveMade(coord[0], coord[1], coord[2]);
		moveMade = true;
		this.notifyAll();
	}
	
	/**
	 * Makemove for humanplayer, also turns off the timer.
	 * @param username name of humanplayer, is unique so can be used to identify player
	 * @param x, x-coordinate of move
	 * @param y, y-coordinate of move
	 * @param z, z-coordinate of move
	 */
	public synchronized void makeMove(String username, int x, int y, int z) {
		timer.cancel();
		for (Player p: players) {
			if (p.getName().equals(username)) {
				if (board.isValidMove(x, y, z)) {
					timer.cancel();
					board.setField(x, y, z, p.getMark());
					informMoveMade(x, y, z);
					moveMade = true;
					this.notifyAll();
				} else {
					((HumanPlayer) p).getHandler().writeOutput(Protocol.ERROR_INVALIDMOVE + Protocol.DELIMITER + x + Protocol.DELIMITER + y + Protocol.DELIMITER + z);
				}
			}
		}
	}

	
	@Override
	public void run() {
		//wait for both players to be ready
		boolean ready = false;
		while (!ready) {
			ready = true;
			for (Player p: players) {
				if (p instanceof HumanPlayer && ((HumanPlayer) p).getHandler().getStatus() != ClientHandler.ClientStatus.IN_GAME) {
					ready = false;
					break;
				}
			}
		}
		timer.cancel();
		
		//start game
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
			}
			
			updatePlayerIndex();
			moveMade = false;
		}
		
		//game is finished
		String msg = Protocol.GAMEOVER;
		if (board.isWinner(players[0].getMark())) {
			msg += Protocol.DELIMITER + players[0].getName();
		} else if (board.isWinner(players[1].getMark())) {
			msg += Protocol.DELIMITER + players[1].getName();
		}
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				((HumanPlayer) p).getHandler().writeOutput(msg);
				((HumanPlayer) p).getHandler().setStatus(ClientHandler.ClientStatus.IN_LOBBY);
			}
		}
	}
	
	public synchronized void updatePlayerIndex() {
		while (!moveMade) {
			try {
				this.wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		currentPlayerIndex = (currentPlayerIndex + 1) % 2;
	}
	
	public void informMoveMade(int x, int y, int z) {
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				((HumanPlayer) p).getHandler().writeOutput(Protocol.SETMOVE + Protocol.DELIMITER + currentPlayer().getName() + Protocol.DELIMITER + x + Protocol.DELIMITER + y + Protocol.DELIMITER + z);
			}
		}
	}
	
	public void setFirstTimeout() {
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				ClientHandler handler = ((HumanPlayer) p).getHandler();
				timer.schedule(new TimerTask() {
					public void run() {
						//TODO: maybe change this
						handler.writeOutput(Protocol.GAMEOVER);
						handler.setStatus(ClientHandler.ClientStatus.IN_LOBBY);
					}
				}, 20 * 1000);
			}
		}
	}
	
	public void setTimeout() {
		timer = new Timer();
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				ClientHandler handler = ((HumanPlayer) p).getHandler();
				timer.schedule(new TimerTask() {
					public void run() {
						handler.writeOutput(Protocol.ERROR_USERQUIT + Protocol.DELIMITER + currentPlayer().getName());
						handler.setStatus(ClientHandler.ClientStatus.IN_LOBBY);
					}
				}, 20 * 1000);
			}
		}	
	}
}
