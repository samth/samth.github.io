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
(define asumu @a[href: "http://www.ccs.neu.edu/home/asumu"]{Asumu Takikawa})
(define krhari @a[href: "http://www.ccs.neu.edu/home/krhari"]{Hari Prashanth K R})
(define sstrickl @a[href: "http://www.ccs.neu.edu/home/sstrickl"]{T. Stephen Strickland})
(define dherman @a[href: "http://www.ccs.neu.edu/home/dherman"]{Dave Herman})
(define dvh @a[href: "http://www.cs.umd.edu/~dvanhorn/"]{David Van Horn})
(define rmc @a[href: "http://www.ccs.neu.edu/~ryan"]{Ryan Culpepper})
(define robby @a[href: "http://www.eecs.northwestern.edu/~robby"]{Robert Bruce Findler})
(define chrdimo @a[href: "http://people.seas.harvard.edu/~chrdimo/"]{Christos Dimoulas})
(define cce @a[href: "http://www.ccs.neu.edu/~cce"]{Carl Eastlund})
(define jay @a[href: "http://jeapostrophe.github.io/"]{Jay McCarthy})
(define jbc @a[href: "http://www.brinckerhoff.org/clements/"]{John Clements})
(define tonyg @a[href: "http://homepages.kcbbs.gen.nz/tonyg/"]{Tony Garnock-Jones})

(define cfbolz "Carl Friedrich Bolz")
(define jsiek "Jeremy G. Siek")
(define rrnewton "Ryan Newton")
(define lkuper "Lindsey Kuper")
(define krono "Tobias Pape")
(define atodd "Aaron Todd")
(define eli "Eli Barzilay")
(define sk "Shriram Krishnamurthi")
(define rxg "Ronald Garcia")

(define matteo "Matteo Cimini")
(define vitousek "Michael M. Vitousek")

;; New people mentioned frequently in recent papers
(define phuc @a[href: "https://pcnguyen.github.io/"]{Phuc C. Nguyen})
(define spall @a[href: "https://github.com/SarahSpall"]{Sarah Spall})
(define bgreenman @a[href: "https://www.ccs.neu.edu/home/types/"]{Ben Greenman})
(define akent @a[href: "https://andmkent.com/"]{Andrew M. Kent})
(define cameron-moy "Cameron Moy")
(define rajan-walia "Rajan Walia")
(define yuquan-fu "Yuquan Fu")
(define chaitanya "Chaitanya S. Koparkar")
(define ambrose @a[href: "https://ambrosebs.com/"]{Ambrose Bonnaire-Sergeant})
(define rowan-davies "Rowan Davies")
(define thomas-gilray @a[href: "http://www.cs.umd.edu/~tgilray/"]{Thomas Gilray})
(define michael-vollmer "Michael Vollmer")
(define neil-mitchell @a[href: "https://ndmitchell.com/"]{Neil Mitchell})
(define chung-chieh-shan @a[href: "https://homes.sice.indiana.edu/ccshan/"]{Chung-chieh Shan})
(define praveen-narayanan "Praveen Narayanan")
(define jacques-carette "Jacques Carette")
(define joshua-crotts @a[href: "https://joshuacrotts.us/"]{L. Joshua Crotts})
(define cameron-swords "Cameron Swords")
(define amr-sabry @a[href: "https://homes.luddy.indiana.edu/sabry/"]{Amr Sabry})
