package connectfour;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class GeniusStrategy implements Strategy {

	private String name;
	private String[] computerNames = {"Tariq", "Rutger"};
	private Map<Mark, Map<Board, Double>> cache = new HashMap<Mark, Map<Board, Double>>();
	
	public GeniusStrategy() {
		this.name = computerNames[(int) (Math.random()*computerNames.length)];
		cache.put(Mark.XX, new HashMap<Board, Double>());
		cache.put(Mark.OO, new HashMap<Board, Double>());
	}
	
	@Override
	public String getStrategyName() {
		return this.name;
	}

	@Override
	public int determineMove(Board board, Mark mark) {
		int bestMove = 0;
		double bestMoveValue = -1;
		for (int move = 0; move < board.getDim() * board.getDim(); move++) {
			Board copyBoard = board.deepCopy();
			int field = Player.fall(copyBoard, move);
			double fieldValue;
			if (field != -1) {
				System.out.println(field);
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
		if (!cache.get(mark).containsKey(board)) {
			if (board.isWinner(mark)) {
				cache.get(mark).put(board, 1.0);
			} else if (board.isFull()) {
				cache.get(mark).put(board, 0.0);
			} else {
				//recursion
				List<Integer> possibleMoves = new ArrayList<Integer>();
				for (int move = 0; move < board.getDim() * board.getDim(); move++) {
					int field = Player.fall(board, move);
					if (field != -1) {
						possibleMoves.add(field);
					}
				}
				 //initial value
				double value = 0.0;
				for (int move: possibleMoves) {
					Board copyBoard = board.deepCopy();
					copyBoard.setField(move, mark.other());
					value -= valueBoardMark(copyBoard, mark.other());
				}
				cache.get(mark).put(board, value / possibleMoves.size());
			}
		}
		return cache.get(mark).get(board);
	}
	
	
	public static void main(String[] args) {
		Board board = new Board(3);
		Strategy s = new GeniusStrategy();
		System.out.println(s.determineMove(board, Mark.XX));
	}
}
