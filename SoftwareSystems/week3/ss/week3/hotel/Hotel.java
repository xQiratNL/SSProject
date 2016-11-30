package ss.week3.hotel;

public class Hotel {
	
	//--------Instance variables-----------
	private String name; //name of the hotel
	private Room room1; //first room of two
	private Room room2; //second room of two
	private Password password; //password of hotel
	
	//------------Generator----------------
	public Hotel(String theName) {
		name = theName;
		room1 = new Room(1);
		room2 = new Room(2);
		password = new Password();
	}
	
	//-----------Commands------------------
	
	public Room checkIn(String thePassword, String theName) {
		Room newRoom = getFreeRoom();
		if (password.testWord(thePassword) && newRoom != null && getRoom(theName) == null) {
			(new Guest(theName)).checkin(newRoom);
			return newRoom;
		} else {
			return null;
		}
		
	}
	
	public void checkOut(String theName) {
		if (getRoom(theName) != null) {
			getRoom(theName).getSafe().deactivate();
			getRoom(theName).getGuest().checkout();
		}
	}
	
	//-----------Queries-------------------
	
	public Room getFreeRoom() {
		if (room1.getGuest() == null) {
			return room1;
		} else if (room2.getGuest() == null) {
			return room2;
		} else {
			return null;
		}
	}
	
	public Room getRoom(String theName) {
		if (room1.getGuest() != null && room1.getGuest().getName().equals(theName)) {
			return room1;
		} else if (room2.getGuest() != null && room2.getGuest().getName().equals(theName)) {
			return room2;
		} else {
			return null;
		}
	}
	
	public Password getPassword() {
		return password;
	}
	
	public String getName() {
		return name;
	}
	
	public String toString() {
		String nameString = "Name of hotel: " + this.name + "\n";
		String safe1String = "Safe open: " + room1.getSafe().isOpen() + ", Safe active: "
				+ room1.getSafe().isActive() + "\n";
		String safe2String = "Safe open: " + room2.getSafe().isOpen() + ", Safe active: "
				+ room2.getSafe().isActive();
		String guest1String = "empty";
		if (room1.getGuest() != null) {
			guest1String = room1.getGuest().toString();
		}
		String guest2String = "empty";
		if (room2.getGuest() != null) {
			guest2String = room2.getGuest().toString();
		}
		String room1String = room1.toString() + ": " + guest1String + ", " + safe1String;
		String room2String = room2.toString() + ": " + guest2String + ", " + safe2String;
		return nameString + room1String + room2String;
	}
}
