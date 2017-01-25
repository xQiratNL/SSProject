package connectfour;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

public class GeniusStrategy implements Strategy {

	private String name;
	private String[] computerNames = {"Tariq", "Rutger"};
	private Map<Mark, Map<String, Double>> cache = new HashMap<Mark, Map<String, Double>>();
	
	public GeniusStrategy() {
		this.name = computerNames[(int) (Math.random()*computerNames.length)];
	}
	
	@Override
	public String getStrategyName() {
		return this.name;
	}

	@Override
	public int determineMove(Board board, Mark mark) {
		cache.put(Mark.XX, new TreeMap<String, Double>());
		cache.put(Mark.OO, new TreeMap<String, Double>());
		int bestMove = (new SmartStrategy()).determineMove(board, mark);
		double bestMoveValue = Integer.MIN_VALUE;
		for (int move = 0; move < board.getDim() * board.getDim(); move++) {
			Board copyBoard = board.deepCopy();
			int field = Player.fall(copyBoard, move);
			double fieldValue;
			if (field != -1) {
				copyBoard.setField(field, mark);
				fieldValue = valueBoardMark(copyBoard, mark);
				if (fieldValue > bestMoveValue) {
					bestMove = field;
					bestMoveValue = fieldValue;
				}
			} //else invalid move
		}
		return bestMove;
	}
	
	public double valueBoardMark(Board board, Mark mark) {
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
					int field = Player.fall(board, move);
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
	
	
	public static void main(String[] args) {
		Board board = new Board(3);
		//System.out.println(board.toString());
		Strategy s = new GeniusStrategy();
		Mark mark = Mark.XX;
		while (!board.gameOver()) {
			int move = s.determineMove(board, mark);
			board.setField(move, mark);
			mark = mark.other();
			System.out.println(board.toString());
		}
	}
}
