package cf.model;

import java.util.Observable;

public class Board extends Observable {
	
	private static final String GRID_DELIM = "\t";
	private static final String FIELD_DELIM = "\t| ";

	private String[] numbering;
	private String line;
	private int dim;
	private int size;
	private Mark[] fields;
	
	//@private invariant numbering.length == size;
	//@private invariant size == dim * dim *dim;
	//@private invariant fields.length == size;
	//@public invariant (\forall int x, y, z; 0 <= x && x < getDim() && 0 <= y && y < getDim() && 0 < z && z < getDim() && getField(x, y,z) != Mark.EMPTY; getField(x, y, z - 1) != Mark.EMPTY); 
	
	//--Constructors--------
	/**
	 * Creates board with empty marks.
	 * 
	 * @param dim dimension of the board, at least three
	 */
	//@ requires dim > 1;
	//@ ensures (\forall int i; 0 <= i && i < getSize(); getField(i) == Mark.EMPTY);
	//@ ensures getDim() == dim;
	//@ ensures getSize() == dim * dim * dim;
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
	/*@ pure */public void numbering() {
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
	/*@ pure */private String[][] boardStatus() {
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
	//@ ensures (\forall int i; 0 <= i && i < getSize(); getField(i) == Mark.EMPTY);
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
	//@ ensures calculateID() == \result.calculateID();
	/*@ pure */public Board deepCopy() {
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
	//@ requires isField(x, y, z) == true;
	//@ ensures \result == getDim() * getDim() * z + getDim() * y + x;
	/*@ pure */ public int index(int x, int y, int z) {
		return dim * dim * z + dim * y + x;
	}
	
	/**
	 * Calculates the coordinates on the board for a given index.
	 * @param index, index of the field on the board
	 * @return array of {x, y, z} coordinates which correspond to the field.
	 */
	//@ requires isField(index) == true;
	//@ ensures index(\result[0], \result[1], \result[2]) == index;
	/*@ pure */public int[] coordinates(int index) {
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
	//@ ensures \result == (0 <= index(x, y, z) && index(x, y, z) < getSize());
	/*@pure */public boolean isField(int x, int y, int z) {
		return 0 <= index(x, y, z) && index(x, y, z) < size;
	}
	
	/**
	 * Returns true of the tuple is a valid field on the board.
	 * @param index, index of the field
	 * @return true if valid.
	 */
	//@ ensures \result == (0 <= index && index < getSize());
	/*@ pure */public boolean isField(int index) {
		return 0 <= index && index < size;
	}
	
	/**
	 * Returns value of field
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return Mark or empty on current field.
	 */
	//@ requires isField(x, y, z);
	/*@ pure */public Mark getField(int x, int y, int z) {
		return fields[index(x, y, z)];
	}
	
	/**
	 * Returns value of field
	 * @param index, index of the field.
	 * @return Mark on current field.
	 */
	//@ requires isField(index);
	/*@ pure */ public Mark getField(int index) {
		return fields[index];
	}
	
	/**
	 * Returns true of field is empty.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return true of empty.
	 */
	//@ requires isField(x, y, z);
	//@ ensures \result == (getField(x, y, z) == Mark.EMPTY);
	/*@ pure */public boolean isEmptyField(int x, int y, int z) {
		return getField(x, y, z).isEmpty();
	}
	
	/**
	 * Returns true of field is empty.
	 * @param index, index of a given field.
	 * @return true of empty.
	 */
	//@ requires isField(index);
	//@ ensures \result == (getField(index) == Mark.EMPTY);
	/*@ pure */public boolean isEmptyField(int index) {
		return fields[index].isEmpty();
	}
	
	/**
	 * Boolean value stating whether or not the move was valid.
	 * @param x, x-coordinate
	 * @param y, y-coordinate
	 * @param z, z-coordinate
	 * @return true if field exists, is empty and z=0 or field below not empty.
	 */
	//@ ensures \result == (isField(x, y, z) && isEmptyField(x,y,z) && (z ==0 || !isEmptyField(x, y, z-1)));
	/*@ pure */public boolean isValidMove(int x, int y, int z) {
		if(!(isField(x, y, z) && isEmptyField(x, y, z))) {
			return false;
		} else if (z == 0 || !isEmptyField(x , y, z - 1)){
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Returns true if board is full.
	 * @return true if board is full.
	 */
	//@ ensures \result == (\forall int i; 0 <= i && i < getDim(); getField(i) != Mark.EMPTY);
	/*@ pure */public boolean isFull() {
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
	//@ requires getField(x, y, z) == Mark.EMPTY;
	//@ ensures getField(x,y,z) == mark;
	//@ ensures (\forall int a,b,c; isField(a,b,c) == true && !(a==x && b==y && c==z); \old(getField(a,b,c)) == getField(a,b,c));
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
	//@ requires getField(index) == Mark.EMPTY;
	//@ ensures getField(index) == mark;
	//@ ensures (\forall int x; isField(x) == true && x != index ; \old(getField(x)) == getField(x));
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
	//@ ensures \result == hasRow(mark) || hasColumn(mark) || hasBar(mark) || hasXDiagonal(mark) || hasYDiagonal(mark) || hasZDiagonal(mark) || hasCrossDiagonal(mark);
	/*@ pure */public boolean isWinner(Mark mark) {
		return hasRow(mark) || hasColumn(mark) || hasBar(mark) || hasXDiagonal(mark) || hasYDiagonal(mark) || hasZDiagonal(mark) || hasCrossDiagonal(mark);
	}
	
	/**
	 * Returns true if given mark has a row on the board.
	 * @param mark, mark of player.
	 * @return true if player of mark has won.
	 */
	//@ ensures \result == (\forall int z, y; 0 <= z && z < getDim() && 0 <= y && y <= getDim(); (\forall int x; isField(x, y, z) == true; getField(x,y,z)==mark));
	/*@ pure*/public boolean hasRow(Mark mark) {
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
	//@ ensures \result == (\forall int x, z; 0 <= x && x < getDim() && 0 <= z && z <= getDim(); (\forall int y; isField(x, y, z) == true; getField(x,y,z)==mark));
	/*@ pure*/public boolean hasColumn(Mark mark) {
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
	//@ ensures \result == (\forall int x, y; 0 <= x && x < getDim() && 0 <= y && y <= getDim(); (\forall int z; isField(x, y, z) == true; getField(x,y,z)==mark));
	/*@ pure*/public boolean hasBar(Mark mark) {
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
	//@ ensures (\forall int z; 0 <= z && z < getDim(); (\forall int i; isField(i, i, z) == true; getField(i,i,z)==mark)) ==> \result == true;
	//@ ensures (\forall int z; 0 <= z && z < getDim(); (\forall int i; isField(i, getDim() - 1 - i, z) == true; getField(i,getDim() - 1 - i,z)==mark)) ==> \result == true;
	/*@ pure*/public boolean hasZDiagonal(Mark mark) {
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
	//@ ensures (\forall int y; 0 <= y && y < getDim(); (\forall int i; isField(i, y, i) == true; getField(i,y,i)==mark)) ==> \result == true;
	//@ ensures  (\forall int y; 0 <= y && y < getDim(); (\forall int i; isField(i, y, getDim() -1 - i) == true; getField(i,y,getDim() -1 -i)==mark)) ==> \result == true;
	/*@ pure*/public boolean hasYDiagonal(Mark mark) {
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
	//@ ensures (\forall int x; 0 <= x && x < getDim(); (\forall int i; isField(x,i,i) == true; getField(x,i,i)==mark)) ==> \result == true;
	//@ ensures (\forall int x; 0 <= x && x < getDim(); (\forall int i; isField(x,i,getDim() -1 -i) == true; getField(x,i,getDim() -1 -i)==mark)) ==> \result == true;
	/*@ pure*/public boolean hasXDiagonal(Mark mark) {
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
	//@ ensures (\forall int i; isField(i,i,i); getField(i,i,i) == mark) ==> \result == true;
	//@ ensures (\forall int i; isField(i,i,getDim() - 1 -i); getField(i,i,getDim() -1 -i) == mark) ==> \result == true;
	//@ ensures (\forall int i; isField(i,getDim() - 1 -i,getDim() - 1 -i); getField(i,getDim() - 1 -i,getDim() - 1 -i) == mark) ==> \result == true;
	//@ ensures (\forall int i; isField(i,getDim() - 1 -i,i); getField(i,getDim() - 1 -i,i) == mark) ==> \result == true;
	/*@ pure*/public boolean hasCrossDiagonal(Mark mark) {
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
	//@ ensures \result == (isWinner(Mark.OO) || isWinner(Mark.XX));
	/*@ pure*/public boolean hasWinner() {
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
	//@ ensures \result == (isFull() || hasWinner());
	/*@ pure*/public boolean gameOver() {
		return this.isFull() || this.hasWinner();
	}
	
	/**
	 * Returns a String representation of the input that can be given for the board, as well
	 * as the current status of the board.
	 */
	/*@ pure*/public String toString() {
		
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
	//@ ensures \result > 1;
	/*@ pure */public int getDim() {
		return dim;
	}
	
	/**
	 * @return size of the board
	 */
	//@ ensures \result >1;
	/*@ pure */ public int getSize() {
		return size;
	}

	/**
	 * Calculates unique identifier for the board in it's current status.
	 * @return string identifying the board in its current state.
	 */
	/*@ pure */public String calculateID() {
		String id = "";
		for (int i = 0; i < size; i++) {
			id += fields[i].toString();
		}
		return id;
	}

	
	/**
	 * Makes a move fall. e.g. gets the fallen position for a move.
	 * @param move	the move in the x,y plane (index)
	 * 
	 * @return the index of the fallen place, or -1 if the vertical bar is full already and no move is possible here.
	 */
	//@	requires move < getDim() * getDim();
	//@ requires isField(move);
	/*@ pure*/public int fall(int move) {
		int[] xyz = coordinates(move);
		int zcoord = 0;
		boolean valid = isValidMove(xyz[0], xyz[1], zcoord);
		while (!valid && zcoord < getDim() - 1) {
			valid = isValidMove(xyz[0], xyz[1], (++zcoord));
		}
		if (valid) {
			return index(xyz[0], xyz[1], zcoord);
		} else {
			return -1;
		}
	}
	
}
