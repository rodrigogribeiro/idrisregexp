default: all

all: clean
	idris -o igrep Main.idr -p effects -p lightyear --typeintype

clean:
	rm igrep
	rm *.ibc
