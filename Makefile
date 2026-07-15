CXX ?= g++
CPPFLAGS ?=
# Vertex enumeration benefits substantially from native vector instructions.
# These variables remain overridable, e.g. `make CXXFLAGS='...' LDFLAGS='...'`.
CXXFLAGS ?= -std=c++17 -O3 -march=native -flto -DNDEBUG -Wall -Wextra -Wpedantic -Wconversion -Wshadow
LDFLAGS ?= -flto
LDLIBS ?=

TARGET := code
SOURCE := code.cpp

.PHONY: all smoke paper-result-1 paper-result-2 paper-result-3 paper-results clean help

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(SOURCE) $(LDFLAGS) $(LDLIBS) -o $(TARGET)

smoke: $(TARGET)
	./$(TARGET) 4 2 5

paper-result-1: $(TARGET)
	./$(TARGET) 10 2 13

paper-result-2: $(TARGET)
	./$(TARGET) 25 13 26

paper-result-3: $(TARGET)
	./$(TARGET) 51 26 40

paper-results: $(TARGET)
	./$(TARGET) 10 2 13
	./$(TARGET) 25 13 26
	./$(TARGET) 51 26 40

clean:
	$(RM) $(TARGET)

help:
	@echo "Targets:"
	@echo "  all             Build the optimized executable (default)."
	@echo "  smoke           Run a small, fast verification instance."
	@echo "  paper-result-1  Run (k,S) = (10,{2,...,12})."
	@echo "  paper-result-2  Run (k,S) = (25,{13,...,25})."
	@echo "  paper-result-3  Run (k,S) = (51,{26,...,39})."
	@echo "  paper-results   Run all three paper instances sequentially."
	@echo "  clean           Remove the compiled executable."
