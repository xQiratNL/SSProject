package connectfour;

public class Board {
	
	public static final int FOUR = 4;
	//TODO: Add other statics.

	private int dim;
	private int size;
	private Mark[] fields;
	
	//--Constructors--------
	/**
	 * Creates board with empty marks.
	 */
	public Board(int dim) {
		this.dim = dim;
		this.size = dim * dim * dim;
		fields = new Mark[size];
		reset();
	}
	
	/**
	 * Sets content of all fields to EMPTY;
	 */
	public void reset() {
		for (int i = 0; i < size; i++) {
			fields[i] = Mark.EMPTY;
		}
	}
	/**
	 * Creates deep copy of this field.
	 * @return deep copy of this board.
	 */
	public Board deepCopy() {
		Board newBoard = new Board(dim);
		newBoard.fields = this.fields.clone();
		return newBoard;
	}
	
	/**
	 * Calculates the index of linear array of fields from a tuple.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return 0<=index<size
	 */
	public int index(int x, int y, int z) {
		return dim * dim * z + dim * y + x;
	}
	
	public int[] coordinates(int index) {
		int z = index / dim * dim;
		int y = (index - z) / dim;
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
		return 0 <= index(x, y, z) && index(x, y, z) < size;
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
		for (int i = 0; i < size; i++) {
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
		for (int z = 0; z < dim; z++) {
			for (int y = 0; y < dim; y++) {
				int nrMark = 0;
				for (int x = 0; x < dim; x++) {
					if (getField(x, y, z).equals(mark)) {
						nrMark++;
					}
				}
				if (nrMark >= FOUR) {
					return true;
				}
			}
		}
		//nothing found;
		return false;
	}
	
	public boolean hasColumn(Mark mark) {
		for (int z = 0; z < dim; z++) {
			for (int x = 0; x< dim; x++) {
				int nrMark = 0;
				for (int y = 0; y < dim; y++) {
					if (getField(x, y, z).equals(mark)) {
						nrMark++;
					}
				}
				if (nrMark >= FOUR) {
					return true;
				}
			}
		}
		//nothing found;
		return false;
	}
	
	public boolean hasBar(Mark mark) {
		for (int x = 0; x < dim; x++) {
			for (int y = 0; y < dim; y++) {
				int nrMark = 0;
				for (int z = 0; z < dim; z++) {
					if (getField(x, y, z).equals(mark)) {
						nrMark++;
					}
				}
				if (nrMark >= FOUR) {
					return true;
				}
			}
		}
		//nothing found;
		return false;
	}
	
	public boolean hasZDiagonal(Mark mark) {
		for (int z = 0; z < dim; z++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(i, i, z).equals(mark)) {
					nrMark++;
				}
			}
			if (nrMark >= FOUR) {
				return true;
			}
		}
		//other diagonal
		for (int z = 0; z < dim; z++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(i, dim - 1 - i, z).equals(mark)) {
					nrMark++;
				}
			}
			if (nrMark >= FOUR) {
				return true;
			}
		}
		//nothing found
		return false;
	}
	
	public boolean hasYDiagonal(Mark mark) {
		for (int y = 0; y < dim; y++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(i, y, i).equals(mark)) {
					nrMark++;
				}
			}
			if (nrMark >= FOUR) {
				return true;
			}
		}
		//other diagonal
		for (int y = 0; y < dim; y++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(i, y , dim - 1 - i).equals(mark)) {
					nrMark++;
				}
			}
			if (nrMark >= FOUR) {
				return true;
			}
		}
		//nothing found
		return false;
	}
	
	public boolean hasXDiagonal(Mark mark) {
		for (int x = 0; x < dim; x++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(x, i, i).equals(mark)) {
					nrMark++;
				}
			}
			if (nrMark >= FOUR) {
				return true;
			}
		}
		//other diagonal
		for (int x = 0; x < dim; x++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(x, i , dim - 1 - i).equals(mark)) {
					nrMark++;
				}
			}
			if (nrMark >= FOUR) {
				return true;
			}
		}
		//nothing found
		return false;
	}
	
	public boolean hasCrossDiagonal(Mark mark) {
		int nrMark = 0;
		//first diagonal
		for (int i = 0; i < dim; i++) {
			if (getField(i, i, i).equals(mark)) {
				nrMark++;
			}
		}
		if (nrMark >= FOUR) {
			return true;
		}
		
		//second diagonal
		for (int i = 0; i < dim; i++) {
			if (getField(i, i, dim - 1 - i).equals(mark)) {
				nrMark++;
			}
		}
		if (nrMark >= FOUR) {
			return true;
		}
		
		//third diagonal
		for (int i = 0; i < dim; i++) {
			if (getField(i, dim - 1 - i, i).equals(mark)) {
				nrMark++;
			}
		}
		if (nrMark >= FOUR) {
			return true;
		}
		
		//fourth diagonal
		for (int i = 0; i < dim; i++) {
			if (getField(i, dim - 1 - i, dim - 1 - i).equals(mark)) {
				nrMark++;
			}
		}
		if (nrMark >= FOUR) {
			return true;
		}
		
		return false;
	}
	
	public String toString() {
		//TODO: implementation of toString.
		return null;
	}
	
	public int getDim() {
		return dim;
	}
	
	public int getSize() {
		return size;
	}
}
