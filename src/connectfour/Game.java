package connectfour;

public class Game implements Runnable {
	
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
	
	//TODO: implement and make start, play, makemove etc.
	
	public void start() {
		
	}
	
	private void reset() {
		currentPlayerIndex = 0;
		board.reset();
	}
	
	private void play() {
		//TODO: implement
	}
	
	public static void main(String[] args) {
		
	}

	@Override
	public void run() {
		//TODO: implement
		
	}
}
