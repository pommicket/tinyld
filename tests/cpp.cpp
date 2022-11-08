#include <vector>
#include <fstream>
#include <algorithm>
#include <climits>

extern "C" int main() {
	std::vector<int> numbers = {};
	
	std::ofstream cout("/dev/stdout");
	std::ifstream cin("/dev/stdin");
// 	
	while (1) {
		int n = INT_MIN;
		cin >> n;
		if (n == INT_MIN) break;
		numbers.push_back(n);
	}
	
	std::sort(numbers.begin(), numbers.end());
// 	
	for (int n: numbers)
		cout << n << std::endl;
	
	exit(0);
}
