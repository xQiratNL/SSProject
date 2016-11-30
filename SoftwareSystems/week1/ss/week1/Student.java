package ss.week1;

public class Student {
	
	public static void main(String[] argv) {
		Student student = new Student();
		System.out.println(student.passed());
	}
	
	public Student() {
		
	}
	
	public int score() {
		return 80;
	}

	private boolean passed() {
		if (score() >= 70) {
			return true;
		} else {
			return false;
		}
	}
}
