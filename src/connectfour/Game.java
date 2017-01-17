package connectfour;

public class Game {
	
	private Board board;
	private Player[] players;
	private int currentPlayerIndex;
	
	public Game(Player[] players, int dim) {
		this.board = new Board(dim);
		this.players = players;
		currentPlayerIndex = 0;
	}

	public Player currentPlayer() {
		return players[currentPlayerIndex];
	}
	
	//TODO: add start, play, makemove etc.
	public static void main(String[] args) {
		
	}
}
