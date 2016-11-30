package ss.week1.hotel;

/**
 * Guest of hotel which has possibly been checked into a room.
 * @author Tariq
 */

public class Guest {
	// Instance variables
	
	private String name;
	private Room room;
	
	// Constructor

	/**
	 * Creates a <code>Guest</code> with the given name, without a room.
	 * @param n name of the new <code>Guest</code>
	 */	
	public Guest(String n) {
		name = n;
	}
	
	//Queries
	/**
	 * Returns the name of this <code>Guest</code>.
	 */
	public String getName() {
		return this.name;
	}
	
	/**
	 * Returns the current Room in which this <code>Guest</code> is living.
	 * @return the room of this <code>Guest</code>;
	 *         <code>null</code> if this <code>Guest</code>
	 *         is currently not living in a room
	 */
	public Room getRoom() {
		return this.room;
	}

	// Commands
	/**
	 * Assigns a <code>Room</code> to this <code>Guest</code>.
	 * @param r the room that this <code>Guest</code> will rent;
	 *        may not be <code>null</code>
	 * @return <code>true</code> if checkin succeeded;
	 *         <code>false</code> if this <code>Guest</code> already has a <code>Room</code>,
	 *         or <code>r</code> already had a <code>Guest</code>.
	 */
	public boolean checkin(Room r) {
		if (this.room == null && r.getGuest() == null) {
			this.room = r;
			r.setGuest(this);
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Sets the <code>Room</code> of this <code>Guest</code> to <code>null</code>.
	 * Also resets the <code>Guest</code>-reference of the current <code>Room</code>.
	 * @return <code>true</code> if this action succeeded;
	 *         <code>false</code> if <code>Guest</code> does not have a <code>Room</code>
	 *         when this method is called.
	 */
	public boolean checkout() {
		if (this.room == null) {
			return false;
		} else {
			this.room.setGuest(null);
			this.room = null;
			return true;
		}
	}
	
	public String toString() {
		return "Guest" + this.name;
	}
}
