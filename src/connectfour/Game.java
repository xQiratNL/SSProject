package connectfour;

public class Game {
	
	private Board board;
	private Player[] players;
	private int currentPlayerIndex;
	
	public Game(Player[] players, int dim) {
		board = new Board(dim);
		this.players = players;
		currentPlayerIndex = 0;
	}
	
	public boolean hasWinner() {
		for (Player player: players) {
			if (board.isWinner(player.getMark())) {
				return true;
			}
		}
		//no winner
		return false;
	}
	
	public boolean gameOver() {
		return board.isFull() || this.hasWinner();
	}
	
	public Player currentPlayer() {
		return players[currentPlayerIndex];
	}
}
