package cf.game;

import java.util.Observable;

public class Board extends Observable {
	
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
	
	/**
	 * Builds a string which represents the current status of a board.
	 * @return Array of Array of Strings giving the board status.
	 */
	private String[][] boardStatus() {
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
		setChanged();
		notifyObservers();
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
	
	/**
	 * Calculates the coordinates on the board for a given index.
	 * @param index, index of the field on the board
	 * @return array of {x, y, z} coordinates which correspond to the field.
	 */
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
	
	/**
	 * Returns true of the tuple is a valid field on the board.
	 * @param index, index of the field
	 * @return true if valid.
	 */
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
	
	/**
	 * Returns value of field
	 * @param index, index of the field.
	 * @return Mark on current field.
	 */
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
	
	/**
	 * Returns true of field is empty.
	 * @param index, index of a given field.
	 * @return true of empty.
	 */
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
		setChanged();
		notifyObservers();
	}
	
	/**
	 * Sets field index to mark.
	 * @param index, index of field to change.
	 * @param mark, mark of player
	 */
	public void setField(int index, Mark mark) {
		fields[index] = mark;
		setChanged();
		notifyObservers(this);
	}
	
	/**
	 * Returns true if given mark has won the game.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
	public boolean isWinner(Mark mark) {
		return hasRow(mark) || hasColumn(mark) || hasBar(mark) || hasXDiagonal(mark) || hasYDiagonal(mark) || hasZDiagonal(mark) || hasCrossDiagonal(mark);
	}
	
	/**
	 * Returns true if given mark has a row on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
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
	
	/**
	 * Returns true if given mark has a column on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
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
	
	/**
	 * Returns true if given mark has a bar on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
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
	
	/**
	 * Returns true if given mark has a diagonal in the xy-plane on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
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
	
	/**
	 * Returns true if given mark has a diagonal in the xz-plane on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
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
	
	/**
	 * Returns true if given mark has a diagonal in the yz-plane on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
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
	
	/**
	 * Returns true if given mark has a true diagonal on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
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
	
	/**
	 * Returns true if one of the marks on the board has won the game.
	 * @return true of X or O has won the game.
	 */
	public boolean hasWinner() {
		if (this.isWinner(Mark.OO) || this.isWinner(Mark.XX)) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Returns true if one of the marks on the board has won the game, or the board is full.
	 * @return true of X or O has won the game, or no more move can be made.
	 */
	public boolean gameOver() {
		return this.isFull() || this.hasWinner();
	}
	
	/**
	 * Returns a String representation of the input that can be given for the board, as well
	 * as the current status of the board.
	 */
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
	
	/**
	 * @return dimension of the board
	 */
	public int getDim() {
		return dim;
	}
	
	/**
	 * @return size of the board
	 */
	public int getSize() {
		return size;
	}

	/**
	 * Calculates unique identifier for the board in it's current status.
	 * @return string identifying the board in its current state.
	 */
	public String calculateID() {
		String id = "";
		for (int i = 0; i < size; i++) {
			id += fields[i].toString();
		}
		return id;
	}
	
}
