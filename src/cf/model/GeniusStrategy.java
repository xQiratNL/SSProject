package cf.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

public class GeniusStrategy implements Strategy {

	private String name;
	private String[] computerNames = {"Tariq", "Rutger"};
	private Map<Mark, Map<String, Double>> cache = new HashMap<Mark, Map<String, Double>>();
	public static final int DEFAULT_THINK_TIME = 15;
	private int thinkTime;
	private int bestMove;
	private Thread calculatingThread;
	private double bestMoveValue;
	
	/** 
	 * Creates a new strategy with name Rutger/Tariq. This is the best strategy implemented.
	 */
	public GeniusStrategy() {
		this(DEFAULT_THINK_TIME);
	}
	
	/**
	 * Creates a new strategy with name Rutger/Tariq. This is the best strategy implemented.
	 * Has a maximum thinking time in seconds, if it runs out of time, it returns the move that smart strategy would have given.
	 * @param time, maximum thinking time in seconds.
	 */
	public GeniusStrategy(int time) {
		this.name = computerNames[(int) (Math.random()*computerNames.length)];
		thinkTime = time * 1000;
	}
	
	/**
	 * Sets the maximum thinking time of this strategy.
	 * @param t maximum time in seconds.
	 */
	public void setThinkTime(int t) {
		thinkTime = t * 1000;
	}
	
	@Override
	/**
	 * Returns the name of the strategy.
	 */
	public String getStrategyName() {
		return this.name;
	}

	@Override
	/**
	 * Determines a move in xy-plane by calculating the value of the board/mark combination by assuming that opponent makes random move.
	 */
	//TODO: improve
	public int determineMove(Board board, Mark mark) {
		int endTime = (int) System.currentTimeMillis() + thinkTime;
		cache.put(Mark.XX, new TreeMap<String, Double>());
		cache.put(Mark.OO, new TreeMap<String, Double>());
		
		calculatingThread = new Thread() {
			public void run() {
				try {
					bestMoveValue = Integer.MIN_VALUE;
					for (int move = 0; move < board.getDim() * board.getDim(); move++) {
						Board copyBoard = board.deepCopy();
						int field = board.fall(move);
						double fieldValue;
						if (field != -1) {
							copyBoard.setField(field, mark);
							fieldValue = valueBoardMark(copyBoard, mark);
							if (fieldValue > bestMoveValue) {
								bestMove = move;
								bestMoveValue = fieldValue;
							}
						} //else invalid move
					}
				} catch (InterruptedException e) {
					//thread interrupted, for good reasons, so this is no issue.
				}
			}
		};
		calculatingThread.start();
		//wait for the amount of thinking time that is allowed
		while ((int) System.currentTimeMillis() < endTime && calculatingThread.isAlive()) {
			//do nothing
		}
		if (calculatingThread.isAlive()) {//thread didn't finish
			calculatingThread.interrupt();//interrupt thread
			return (new SmartStrategy()).determineMove(board, mark);
		} else {//thread finished
			return bestMove;
		}

	}
	
	/**
	 * Calculates the value of the board/mark combination, taking all possible opponent moves into account
	 * @param board, current board
	 * @param mark, mark to play.
	 * @return value of the board, between -1.0 and 1.0.
	 * @throws InterruptedException 
	 */
	public double valueBoardMark(Board board, Mark mark) throws InterruptedException {
		Thread.sleep(0); //necessary for interrupt to work.
		String id = board.calculateID();
		if (!cache.get(mark).containsKey(id)) {
			if (board.isWinner(mark)) {
				cache.get(mark).put(id, 1.0);
			} else if (board.isFull()) {
				cache.get(mark).put(id, 0.0);
			} else {
				//recursion
				List<Integer> possibleMoves = new ArrayList<Integer>();
				for (int move = 0; move < board.getDim() * board.getDim(); move++) {
					int field = board.fall(move);
					if (field != -1.0) {
						possibleMoves.add(field);
					}
				}
				//check of opponent can win directly
				for (int move: possibleMoves) {
					Board copyBoard = board.deepCopy();
					copyBoard.setField(move, mark.other());
					if (copyBoard.isWinner(mark.other())) {
						cache.get(mark).put(id, -1.0);
						return -1.0;
					}
				}
				
				 //initial value
				double value = 0.0;
				for (int move: possibleMoves) {
					Board copyBoard = board.deepCopy();
					copyBoard.setField(move, mark.other());
					value -= valueBoardMark(copyBoard, mark.other());
				}
				cache.get(mark).put(id, value / possibleMoves.size());
			}
		}
		return cache.get(mark).get(id);
	}

}

