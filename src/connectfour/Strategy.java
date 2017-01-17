package connectfour;

public interface Strategy {
	
	public String getName();

	public int determineMove(Board board, Mark mark);
	
}
