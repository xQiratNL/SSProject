package cf.server;

import java.util.Timer;
import java.util.TimerTask;

import cf.Protocol;
import cf.model.Board;

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
		timer.cancel();
		board.setField(field, player.getMark());
		int[] coord = board.coordinates(field);
		informMoveMade(coord[0], coord[1], coord[2]);
		moveMade = true;
		this.notifyAll();//update player index
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
					this.notifyAll();//update player index
				} else {
					((HumanPlayer) p).getHandler().writeOutput(Protocol.ERROR_INVALIDMOVE + Protocol.DELIMITER + x + Protocol.DELIMITER + y + Protocol.DELIMITER + z);
				}
			}
		}
	}

	
	@Override
	/**
	 * Starts the game requests moves of players and makes move and if gameover sends message to all players.
	 */
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
		timer.cancel();//turn off timer
		
		//start game
		while (!board.gameOver()) {
			if (currentPlayer() instanceof ComputerPlayer) {//computerplayers turn
				makeMove(currentPlayer(), ((ComputerPlayer) currentPlayer()).determineMove(board));
			} else {//humanplayers turn
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
		
		//game is finished, inform players
		String msg = Protocol.GAMEOVER;
		if (board.isWinner(players[0].getMark())) {
			msg += Protocol.DELIMITER + players[0].getName();
		} else if (board.isWinner(players[1].getMark())) {
			msg += Protocol.DELIMITER + players[1].getName();
		}
		for (Player p: players) {
			if (p instanceof HumanPlayer) {//inform only human players and change status of players
				((HumanPlayer) p).getHandler().writeOutput(msg);
				((HumanPlayer) p).getHandler().setStatus(ClientHandler.ClientStatus.IN_LOBBY);
			}
		}
	}
	
	/**
	 * Change playerindex when a move is made, while not made whait on move made.
	 */
	public synchronized void updatePlayerIndex() {
		while (!moveMade) {
			try {
				this.wait();
			} catch (InterruptedException e) {//shouldn't happen
				System.out.println(e.getMessage());
			}
		}
		currentPlayerIndex = (currentPlayerIndex + 1) % 2;
	}
	
	/**
	 * inform all clients in game of the move made
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 */
	public void informMoveMade(int x, int y, int z) {
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				((HumanPlayer) p).getHandler().writeOutput(Protocol.SETMOVE + Protocol.DELIMITER + currentPlayer().getName() + Protocol.DELIMITER + x + Protocol.DELIMITER + y + Protocol.DELIMITER + z);
			}
		}
	}
	
	/**
	 * Players most answer ready/decline within 20 seconds or else userquit message gets send.
	 */
	public void setFirstTimeout() {
		for (Player p: players) {
			if (p instanceof HumanPlayer) {
				ClientHandler handler = ((HumanPlayer) p).getHandler();
				timer.schedule(new TimerTask() {
					public void run() {
						if (handler.getStatus() != ClientHandler.ClientStatus.IN_GAME) {
							handler.decline();
						}
						handler.setStatus(ClientHandler.ClientStatus.IN_LOBBY);
					}
				}, 20 * 1000);
			}
		}	
	}
	
	public void cancelTimer() {
		timer.cancel();
	}
	
	/**
	 * Players most send a move within 20 seconds or else userquit message gets send.
	 */
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
