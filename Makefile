all: index.html

index.html: compiled/main_rkt.zo
	racket main.rkt > index.html
compiled/main_rkt.zo: *.rkt
	raco make -v main.rkt
push: all
	git push gh master
	ssh silo.cs.indiana.edu 'cd html-pub && git pull'
#	ssh login.ccs.neu.edu 'cd .www && git pull'
