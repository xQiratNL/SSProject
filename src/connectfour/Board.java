package connectfour;

public class Board {
	
	private static final String GRID_DELIM = "\t";
	private static final String FIELD_DELIM = "\t| ";

	private String[] numbering;
	private String line;
	private int dim;
	private int size;
	private Mark[] fields;
	
	//--Constructors--------
	/**
	 * Creates board with empty marks.
	 * Requires dim>=4.
	 * 
	 * @param dim dimension of the board
	 */
	//@ dim>=3;
	public Board(int dim) {
		this.dim = dim;
		this.size = dim * dim * dim;
		fields = new Mark[size];
		numbering();
		reset();
	}
	
	/**
	 * Creates the numbering of the fields in the xy-plane.
	 * @return String which represents the numbering.
	 */
	public void numbering() {
		//set line
		line = "--------";
		for (int i = 1; i < dim; i++) {
			line += "+-------";
		}
		//set numbering
		numbering = new String[2 * dim - 1];
		int index = 0;
		//xy-plane
		for (int y = 0; y < dim; y++ ) {
			//one line
			String newLine = " ";
			for (int x = 0; x < dim; x++) {
				newLine += index;
				if (! (x == dim - 1)) {
					newLine += FIELD_DELIM;
				} else {
					newLine += "\t";
				}
				index++;
			}
			newLine += " ";
			numbering[2 * y] = newLine;
			if (!(y == dim - 1)) {
				numbering[2* y + 1] = line;
			}
		}
	}
	
	public String[][] boardStatus() {
		//set numbering
		String[][] status = new String[dim][2 * dim - 1];
		for (int z = 0; z < dim; z++) {
			//xy-plane
			for (int y = 0; y < dim; y++ ) {
				//one line
				String newLine = " ";
				for (int x = 0; x < dim; x++) {
					newLine += getField(x, y, z);
					if (! (x == dim - 1)) {
						newLine += FIELD_DELIM;
					} else {
						newLine += "\t";
					}
				}
				newLine += " ";
				status[z][2 * y] = newLine;
				if (!(y == dim - 1)) {
					status[z][2* y + 1] = line;
				}
			}
		}
		return status;
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
		int z = index / (dim * dim);
		int y = (index - z * dim * dim) / dim;
		int x = index - z * dim * dim - y * dim;
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
	
	public boolean isField(int index) {
		return 0 <= index && index < size;
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
	
	public Mark getField(int index) {
		return fields[index];
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
	
	public boolean isEmptyField(int index) {
		return fields[index].isEmpty();
	}
	
	/**
	 * Boolean value stating whether or not the move was valid.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return true if field exists, is empty and z=0 or field below not empty.
	 */
	public boolean isValidMove(int x, int y, int z) {
		if(!(isField(x, y, z) && isEmptyField(x, y, z))) {
			return false;
		} else if (z == 0 || !(isEmptyField(x , y, z - 1))){
			return true;
		} else {
			return false;
		}
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
	
	/**
	 * Sets field index to mark.
	 * @param index, index of field to change.
	 * @param mark, mark of player
	 */
	public void setField(int index, Mark mark) {
		fields[index] = mark;
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
					} else {
						break;
					}
				}
				if (nrMark == dim) {
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
					} else {
						break;
					}
				}
				if (nrMark == dim) {
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
					} else {
						break;
					}
				}
				if (nrMark == dim) {
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
				} else {
					break;
				}
			}
			if (nrMark == dim) {
				return true;
			}
		}
		//other diagonal
		for (int z = 0; z < dim; z++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(i, dim - 1 - i, z).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == dim) {
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
				} else {
					break;
				}
			}
			if (nrMark == dim) {
				return true;
			}
		}
		//other diagonal
		for (int y = 0; y < dim; y++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(i, y , dim - 1 - i).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == dim) {
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
				} else {
					break;
				}
			}
			if (nrMark == dim) {
				return true;
			}
		}
		//other diagonal
		for (int x = 0; x < dim; x++) {
			int nrMark = 0;
			for (int i = 0; i < dim; i++) {
				if (getField(x, i , dim - 1 - i).equals(mark)) {
					nrMark++;
				} else {
					break;
				}
			}
			if (nrMark == dim) {
				return true;
			}
		}
		//nothing found
		return false;
	}
	
	public boolean hasCrossDiagonal(Mark mark) {
		//first diagonal
		int nrMark = 0;
		for (int i = 0; i < dim; i++) {
			if (getField(i, i, i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == dim) {
			return true;
		}
		
		//second diagonal
		nrMark = 0;
		for (int i = 0; i < dim; i++) {
			if (getField(i, i, dim - 1 - i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == dim) {
			return true;
		}
		
		//third diagonal
		nrMark = 0;
		for (int i = 0; i < dim; i++) {
			if (getField(i, dim - 1 - i, i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == dim) {
			return true;
		}
		
		//fourth diagonal
		nrMark = 0;
		for (int i = 0; i < dim; i++) {
			if (getField(i, dim - 1 - i, dim - 1 - i).equals(mark)) {
				nrMark++;
			} else {
				break;
			}
		}
		if (nrMark == dim) {
			return true;
		}
		
		return false;
	}
	
	public boolean hasWinner() {
		if (this.isWinner(Mark.OO) || this.isWinner(Mark.XX)) {
			return true;
		} else {
			return false;
		}
	}
	
	public boolean gameOver() {
		return this.isFull() || this.hasWinner();
	}
	
	public String toString() {
		
		String string = "Numbering: \n \n";
		
		String[][] status = boardStatus();
		//print numbering
		for (int lineNr = 0; lineNr < 2 * dim -1; lineNr++) {
				string += numbering[lineNr];
			string += "\n";
		}
		string += "\n";
		
		//print z indices
		String tabs = "\t\t\t\t\t";
		for (int i = 4; i < dim; i++) {
			tabs += "\t";
		}
		string += "\t\t";
		for (int z = 0; z < dim; z++) {
			string += "z=" + z + tabs;
		}
		
		string += "\n\n";
		//print status
		for (int lineNr = 0; lineNr < 2 * dim -1; lineNr++) {
			for (int z = 0; z < dim; z++) {
				string += status[z][lineNr] + GRID_DELIM;
			}
			string += "\n";
		}
		return string;
	}
	
	public int getDim() {
		return dim;
	}
	
	public int getSize() {
		return size;
	}
	
	public boolean equals(Object obj) {
		if (obj instanceof Board && ((Board) obj).getDim() == dim) {
			for (int i = 0; i < size; i++) {
				if (fields[i] != ((Board) obj).getField(i)) {
					return false;
				}
			} //all fields equal
			return true;
		} else {
			return false;
		}
	}
	
	public int calculateID() {
		for (int i = 0; i < size; i++) {
			
		}
		return 0;
	}
	
	/**
	public static void main(String[] args) {
		Board board = new Board(4);
		System.out.println(board.toString());
	}
	*/
	
}
