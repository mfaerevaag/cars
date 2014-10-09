# Parallel - Mandatory 1

JC    = javac
JCR   = java

# PKG   = car_control
CLASS = Cars

all: build run

build:
	@echo Building...
	@${JC} -d bin -sourcepath src src/${CLASS}.java

run:
	@echo Running...
	@${JCR} -classpath bin ${CLASS}

.PHONY: build run
