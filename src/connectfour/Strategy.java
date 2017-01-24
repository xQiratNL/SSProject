package connectfour;

public interface Strategy {
	
	public String getStrategyName();

	public int determineMove(Board board, Mark mark);
	
}
