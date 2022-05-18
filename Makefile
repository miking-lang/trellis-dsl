
.PHONY: test clean

main_name=main
exec_name=trellis
mcore_stdlib=${MCORE_STDLIB}

all: build/${main_name}

src/trellis.mc: src/trellis.syn
	mi compile ${mcore_stdlib}/parser/tool.mc
	./tool src/trellis.syn src/trellis.mc
	rm -f tool

build/${main_name}: $(shell find . -name "*.mc") src/trellis.syn src/trellis.mc
	mi compile src/${main_name}.mc
	mkdir -p build
	cp ${main_name} build/${main_name}
	rm ${main_name}

test: build/${main_name}
	@$(MAKE) -s -f test.mk all


clean:
	rm -rf build
	rm src/trellis.mc
