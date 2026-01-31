CXX = g++
CXXFLAGS = -std=c++17 -Wall -Wextra -I../klr -DTEST_ONLY
LDFLAGS = 

test_fromNKI: test_fromNKI.cpp ../klr/fromNKI.hpp
	$(CXX) $(CXXFLAGS) -o test_fromNKI test_fromNKI.cpp $(LDFLAGS)

clean:
	rm -f test_fromNKI 

.PHONY: run_tests clean