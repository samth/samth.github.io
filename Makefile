all:
	racket main.rkt > index.html
push:
	git status && git push
	ssh tank 'cd html-pub && git pull'
