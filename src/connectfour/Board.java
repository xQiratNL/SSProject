package connectfour;

public class Board {
	
	public static final int DIM = 4;
	public static final int SIZE = DIM * DIM * DIM;
	//TODO: Add other statics.

	private Mark[] fields;
	
	//--Constructors--------
	/**
	 * Creates board with empty marks.
	 */
	public Board() {
		fields = new Mark[DIM * DIM * DIM];
		reset();
	}
	
	/**
	 * Sets content of all fields to EMPTY;
	 */
	public void reset() {
		for (int i = 0; i < SIZE; i++) {
			fields[i] = Mark.EMPTY;
		}
	}
	/**
	 * Creates deep copy of this field.
	 * @return deep copy of this board.
	 */
	public Board deepCopy() {
		Board newBoard = new Board();
		newBoard.fields = this.fields.clone();
		return newBoard;
	}
	
	/**
	 * Calculates the index of linear array of fields from a tuple.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return 0<=index<SIZE
	 */
	public int index(int x, int y, int z) {
		return DIM * DIM * z + DIM * y + x;
	}
	
	public int[] coordinates(int index) {
		int z = index / DIM * DIM;
		int y = (index - z) / DIM;
		int x = index - z - y;
		int[] coordinates = {x, y, z};
		return coordinates;
	}
	
	/**
	 * Returns true of the tuple is a valid field on the board.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return true if valid.
	 */
	public boolean isField(int x, int y, int z) {
		return 0 <= index(x, y, z) && index(x, y, z) < SIZE;
	}
	
	/**
	 * Returns value of field
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return Mark or empty on current field.
	 */
	public Mark getField(int x, int y, int z) {
		return fields[index(x, y, z)];
	}
	
	/**
	 * Returns true of field is empty.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return true of empty.
	 */
	public boolean isEmptyField(int x, int y, int z) {
		return getField(x, y, z).isEmpty();
	}
	
	/**
	 * Returns true if board is full.
	 * @return true if board is full.
	 */
	public boolean isFull() {
		for (int i = 0; i < SIZE; i++) {
			if (fields[i].isEmpty()) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * Sets field (x, y, z) to mark.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @param mark, mark of player
	 */
	public void setField(int x, int y, int z, Mark mark) {
		fields[index(x, y, z)] = mark;
	}
	
	public boolean isWinner(Mark mark) {
		return hasRow(mark) || hasColumn(mark) || hasBar(mark) || hasXDiagonal(mark) || hasYDiagonal(mark) || hasZDiagonal(mark) || hasCrossDiagonal(mark);
	}
	
	public boolean hasRow(Mark mark) {
		for (int z = 0; z < DIM; z++) {
			for (int y = 0; y < DIM; y++) {
				int nrMark = 0;
				for (int x = 0; x < DIM; x++) {
					if (getField(x, y, z).equals(mark)) {
						nrMark++;
					} else {
						break;
					}
				}
				if (nrMark == DIM) {
					return true;
				}
			}
		}
		//nothing found;
		return false;
	}
	
	public boolean hasColumn(Mark mark) {
		for (int z = 0; z < DIM; z++) {
			for (int x = 0; x< DIM; x++) {
				int nrMark = 0;
				for (int y = 0; y < DIM; y++) {
					if (getField(x, y, z).equals(mark)) {
						nrMark++;
					} else {
						break;
					}
				}
				if (nrMark == DIM) {
					return true;
				}
			}
		}
		//nothing found;
		return false;
	}
	
	public boolean hasBar(Mark mark) {
		for (int x = 0; x < DIM; x++) {
			for (int y = 0; y < DIM; y++) {
				int nrMark = 0;
				for (int z = 0; z < DIM; z++) {
					if (getField(x, y, z).equals(mark)) {
						nrMark++;
					} else {
						break;
					}
				}
				if (nrMark == DIM) {
					return true;
				}
			}
		}
		//nothing found;
		return false;
	}
	
	public boolean hasZDiagonal(Mark mark) {
		for (int z = 0; z < DIM; z++) {
			int nrMark = 0;
			for (int i = 0; i < DIM; i++) {
				if (getField(i, i, z).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == DIM) {
				return true;
			}
		}
		//other diagonal
		for (int z = 0; z < DIM; z++) {
			int nrMark = 0;
			for (int i = 0; i < DIM; i++) {
				if (getField(i, DIM - 1 - i, z).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == DIM) {
				return true;
			}
		}
		//nothing found
		return false;
	}
	
	public boolean hasYDiagonal(Mark mark) {
		for (int y = 0; y < DIM; y++) {
			int nrMark = 0;
			for (int i = 0; i < DIM; i++) {
				if (getField(i, y, i).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == DIM) {
				return true;
			}
		}
		//other diagonal
		for (int y = 0; y < DIM; y++) {
			int nrMark = 0;
			for (int i = 0; i < DIM; i++) {
				if (getField(i, y , DIM - 1 - i).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == DIM) {
				return true;
			}
		}
		//nothing found
		return false;
	}
	
	public boolean hasXDiagonal(Mark mark) {
		for (int x = 0; x < DIM; x++) {
			int nrMark = 0;
			for (int i = 0; i < DIM; i++) {
				if (getField(x, i, i).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == DIM) {
				return true;
			}
		}
		//other diagonal
		for (int x = 0; x < DIM; x++) {
			int nrMark = 0;
			for (int i = 0; i < DIM; i++) {
				if (getField(x, i , DIM - 1 - i).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == DIM) {
				return true;
			}
		}
		//nothing found
		return false;
	}
	
	public boolean hasCrossDiagonal(Mark mark) {
		int nrMark = 0;
		//first diagonal
		for (int i = 0; i < DIM; i++) {
			if (getField(i, i, i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == DIM) {
			return true;
		}
		
		//second diagonal
		for (int i = 0; i < DIM; i++) {
			if (getField(i, i, DIM - 1 - i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == DIM) {
			return true;
		}
		
		//third diagonal
		for (int i = 0; i < DIM; i++) {
			if (getField(i, DIM - 1 - i, i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == DIM) {
			return true;
		}
		
		//fourth diagonal
		for (int i = 0; i < DIM; i++) {
			if (getField(i, DIM - 1 - i, DIM - 1 - i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == DIM) {
			return true;
		}
		
		return false;
	}
	
	public String toString() {
		//TODO: implementation of toString.
		return null;
	}
}
