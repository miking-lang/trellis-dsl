.PHONY: all

test-files=
test-files+=${wildcard src/*.mc}

# NOTE(Linnea,2022-05-25): Cannot yet be compiled
test-files := $(filter-out src/forward-backward.mc,$(test-files))
test-files := $(filter-out src/viterbi.mc,$(test-files))
test-files := $(filter-out src/parse_data.mc,$(test-files))


all: ${test-files}

${test-files}::
	@./make test $@
