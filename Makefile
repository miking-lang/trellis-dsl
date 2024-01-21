
.PHONY: test examples clean

MAIN_NAME=trellis

all: build/${MAIN_NAME}

build/${MAIN_NAME}: $(shell find . -name "*.mc") src/ast.mc
	mkdir -p build
	mi compile src/${MAIN_NAME}.mc --output build/${MAIN_NAME}

src/ast.mc: src/ast.syn
	mi syn $< $@

#examples: build/${MAIN_NAME}
#	@$(MAKE) -s -f examples.mk all

test: build/${MAIN_NAME}
	@$(MAKE) -s -f test.mk all

clean:
	rm -rf build
	rm src/ast.mc
