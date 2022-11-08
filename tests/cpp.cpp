#include <vector>
#include <iostream>
#include <algorithm>
#include <climits>

extern "C" int main() {
	std::vector<int> numbers = {};
	
	while (1) {
		int n = INT_MIN;
		std::cin >> n;
		if (n == INT_MIN) break;
		numbers.push_back(n);
	}
	
	//std::sort(numbers.begin(), numbers.end());
	
	for (int n: numbers)
		std::cout << n << std::endl;
	
	exit(0);
}
