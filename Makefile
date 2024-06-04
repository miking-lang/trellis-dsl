
.PHONY: test examples clean

MAIN_NAME=trellis
BIN_PATH=$(HOME)/.local/bin
SRC_PATH=$(HOME)/.local/src

default: build/$(MAIN_NAME)

build/$(MAIN_NAME): $(shell find . -name "*.mc") src/parser/ast.mc
	mkdir -p build
	mi compile src/$(MAIN_NAME).mc --output build/$(MAIN_NAME)

src/parser/ast.mc: src/parser/ast.syn
	mi syn $< $@

install: default
	cp build/$(MAIN_NAME) $(BIN_PATH)/$(MAIN_NAME)
	chmod +x $(BIN_PATH)/$(MAIN_NAME)
	mkdir -p $(SRC_PATH)
	cp -rf src/. $(SRC_PATH)/$(MAIN_NAME)

uninstall:
	rm -f $(BIN_PATH)/$(MAIN_NAME)
	rm -rf $(SRC_PATH)

test: build/$(MAIN_NAME)
	@$(MAKE) -s -f test.mk all

clean:
	rm -rf build
	rm src/parser/ast.mc
