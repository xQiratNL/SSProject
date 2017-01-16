package connectfour;

public class Game {

	//TODO: add hasWinner and GameOver (from tictactoe board).
	
	private Board board;
	private Player[] players;
	private int currentPlayer;
	
	public Game(Player[] players) {
		board = new Board();
		this.players = players;
		currentPlayer = 0;
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
}
