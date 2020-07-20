

all: build
.PHONY: all


build:
	go build -mod vendor .

.PHONY: build


vendor:
	go mod vendor -v

.PHONY: vendor
