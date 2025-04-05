all:
	hugo build -d docs

dev:
	hugo serve

.PHONY: all dev
