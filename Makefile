PROJECT_FILE=src/dfyconfig.toml
TARGET = build/compiler
INPUT=input.txt

all:
	dafny run $(PROJECT_FILE) --build $(TARGET) -- $(INPUT)

build:
	dafny build $(PROJECT_FILE) --output $(TARGET)

run:
	dafny run --no-verify $(PROJECT_FILE) --build $(TARGET) -- $(INPUT)

verify:
	dafny verify $(PROJECT_FILE)
