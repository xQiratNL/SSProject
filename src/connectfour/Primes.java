package connectfour;

public class Primes {

	public int[] primes;
	
	public Primes(int size) {
		primes = calculatePrimes(size * 3);
	}
	
	private int[] calculatePrimes(int n) {
		int[] result = new int[n];
		result[0] = 2;
		int i = 3;
		while (result.length < n) {
			valid = true;
			for (int prime: result) {
				if ()
			}
		}
		return result;
	}
}
