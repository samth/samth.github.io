#lang at-exp racket

(provide (all-defined-out))
(require scribble/html)


(define (format-coauthors cos)
  (match cos
     [(list) null]
     [(list c) @span{With @|c|.}]
     [(list a ... b) @span{With @(add-between a ", ") and @|b|.}]))

(define sth "Sam Tobin-Hochstadt")

(define MF @a[href: "http://www.ccs.neu.edu/home/matthias"]{Matthias Felleisen})
(define mflatt @a[href: "http://www.cs.utah.edu/~mflatt"]{Matthew Flatt})
(define stamourv @a[href: "http://www.ccs.neu.edu/home/stamourv"]{Vincent St-Amour})
(define krhari @a[href: "http://www.ccs.neu.edu/home/krhari"]{Hari Prashanth K R})
(define sstrickl @a[href: "http://www.ccs.neu.edu/home/sstrickl"]{T. Stephen Strickland})
(define dherman @a[href: "http://www.ccs.neu.edu/home/dherman"]{Dave Herman})
(define dvh @a[href: "http://www.ccs.neu.edu/home/dvanhorn"]{David Van Horn})
(define rmc @a[href: "http://www.cs.utah.edu/~ryan"]{Ryan Culpepper})
(define robby @a[href: "http://www.eecs.northwestern.edu/~robby"]{Robert Bruce Findler})
(define chrdimo @a[href: "http://www.ccs.neu.edu/~chrdimo"]{Christos Dimoulas})
(define cce @a[href: "http://www.ccs.neu.edu/~cce"]{Carl Eastlund})
(define jay @a[href: "http://faculty.cs.byu.edu/~jay/home/"]{Jay McCarthy})
(define jbc @a[href: "http://www.brinckerhoff.org/clements/"]{John Clements})
