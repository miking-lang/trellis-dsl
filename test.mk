.PHONY: all

test-files=
test-files+=${wildcard src/*.mc}
test-files+=${wildcard src/model/*.mc}
test-files+=${wildcard src/parser/*.mc}
test-files+=${wildcard src/constraints/*.mc}

# NOTE(larshum, 2024-02-15): Main file is tested when compiling
test-files := $(filter-out src/trellis.mc,$(test-files))

all: ${test-files}

${test-files}::
	@./make test $@
