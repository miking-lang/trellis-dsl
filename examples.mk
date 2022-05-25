.PHONY: all

test-files=
test-files+=${wildcard examples/*.trellis}

all: ${test-files}

${test-files}::
	@./make example $@
