#lang at-exp racket

(provide (all-defined-out))
(require scribble/html "people.rkt" "utils.rkt")

@(define (acm id)
   `("ACM DL"
     ,(string-append "http://portal.acm.org/citation.cfm?id=" id)))

@(define (neu id)
   `("PDF"
     ,(string-append "http://www.ccs.neu.edu/racket/pubs/" id ".pdf")))

(struct paper (title co loc date resources))
(struct abstract paper ())
(struct preprint paper ())

(define tr-papers
   (list 
    (paper "Proceedings of the Third Workshop on Script to Program Evolution"
	   (list)
	   "NU CCIS Technical Report NU-CCIS-12-02"
	   "June 2012"
	   `(("PDF" "stop2012-proceedings.pdf")))
    (paper "Complete Monitors for Behavioral Contracts"
           (list chrdimo MF)
           "European Symposium on Programming (ESOP)"
           "March 2012"
           `(,(neu "esop12-dthf")))
    (paper "Typing the Numeric Tower"
           (list stamourv mflatt MF)
           @a[href: "http://research.microsoft.com/en-us/um/people/crusso/padl12/"]{Symposium on Practical Aspects of Declarative Languages (PADL)}
           "January 2012"
           `(,(neu "padl12-stff")))
    (paper "Logical Types for Untyped Languages"
           (list MF)
           @a[href: "http://www.icfpconference.org/icfp2010/index.html"]{International Conference on Functional Programming (ICFP)}
           "September 2010"
           `(,(neu "icfp10-thf") ,(acm "1863561")))

    (preprint "The Design and Implementation of Typed Scheme"
              (list MF)
              @span{Accepted for publication in @a[href: "http://www.brics.dk/~hosc/"]{Higher-Order and Symbolic Computation}}
              "September 2010"
              `(("PDF" "refinement-mitchfest.pdf")
                ("arXiv" "http://arxiv.org/abs/1106.2575"))
              )

    (paper "Functional Data Structures for Typed Racket"
           (list krhari)
           @a[href: "http://www.iro.umontreal.ca/~sfp2010/"]{Workshop on Scheme and Functional Programming}
           "August 2010"
           `(,(neu "sfp10-kth")
             ("PLaneT Package" "http://planet.racket-lang.org/display.ss?package=pfds.plt&owner=krhari")))
    (paper "Typed Scheme: From Scripts to Programs"
           null
           "PhD Dissertation, Northeastern University"
           "January 2010"
           `(,(neu "dissertation-tobin-hochstadt")
             #;("ProQuest" "")))
    (paper "Cycles without pollution: a gradual typing poem"
           (list robby)
           @a[href: "http://wrigstad.com/stop09/"]{1st International Workshop on Script to Program Evolution (STOP)}
           "July 2009"
           `(,(neu "stop09-ft")
             ,(acm "1570506.1570512")))
    (paper "Practical Variable-Arity Polymorphism"
           (list sstrickl MF)
           @a[href: "http://esop09.pps.jussieu.fr/"]{European Symposium on Programming (ESOP)}
           "March 2009"
           `(,(neu "esop09-sthf")
             ("Springer" "http://www.springerlink.com/content/x4l6q4n112425081/")))
    (paper "The Design and Implementation of Typed Scheme"
           (list MF)
           @a[href: "http://www.cs.ucsd.edu/popl/08/"]{Symposium on Principles of Programming Languages (POPL)}
           "January 2008"
           `(,(neu "popl08-thf") 
             ,(acm "1328486")
             ("Formal Models" "https://github.com/samth/popl08-model")))
    (paper "Interlanguage Migration: From Scripts to Programs"
           (list MF)
           @a[href: "http://www.dcl.hpi.uni-potsdam.de/dls2006/openconf.php"]{Dynamic Languages Symposium (DLS)}
           "October 2006"
           `(,(neu "dls06-thf") 
             ,(acm "1176617.1176755")))
    ))

(define macro-papers
   (list
    (paper "Run Your Research: On the Effectiveness of Lightweight Mechanization"
           (list "Casey Klein" jbc chrdimo cce MF mflatt jay "Jon Rafkind" robby)
           @a[href: "http://www.cse.psu.edu/popl/12/"]{Symposium on Principles of Programming Languages (POPL)}
           "January 2012"
           `(("PDF" "http://eecs.northwestern.edu/~robby/lightweight-metatheory/popl2012-kcdeffmrtf.pdf")
             ("Models" "http://eecs.northwestern.edu/~robby/lightweight-metatheory/")))
    (paper "Languages as Libraries"
           (list stamourv rmc mflatt MF)
           @a[href: "http://pldi11.cs.utah.edu/"]{Conference on Programming Language Design and Implementation (PLDI)}
           "June 2011"
           `(,(neu "pldi11-thacff")
             ,(acm "1993514")))
    (preprint "Extensible Pattern Matching in an Extensible Language"
              null
              ""
              "October 2010"
              `(("PDF" "match-ifl-full.pdf")
                ("arXiv" "http://arxiv.org/abs/1106.2578")))
    (abstract "Extensible Pattern Matching in an Extensible Language"
              null
              @a[href: "http://www.cs.uu.nl/wiki/bin/view/IFL2010/WebHome"]{Symposium on Implementation and Application of Functional Languages}
              "September 2010"
              `(("PDF" "ifl-2010-abstract.pdf")
                ("Utrecht Technical Report" "http://www.cs.uu.nl/research/techreps/UU-CS-2010-020.html")))
    (abstract "Where are you going with those types?"
              (list stamourv mflatt MF)
              @a[href: "http://www.cs.uu.nl/wiki/bin/view/IFL2010/WebHome"]{Symposium on Implementation and Application of Functional Languages}
              "September 2010"
              `(("PDF" "http://www.ccs.neu.edu/home/stamourv/ifl10.pdf")                
                ("Utrecht Technical Report" "http://www.cs.uu.nl/research/techreps/UU-CS-2010-020.html")))
    (paper "Advanced Macrology and the Implementation of Typed Scheme"
           (list rmc mflatt)
           @a[href: "http://www.schemeworkshop.org/2007/"]{Workshop on Scheme and Functional Programming}
           "September 2007"
           `(,(neu "scheme2007-cft")
             ("Proceedings" "http://www.schemeworkshop.org/2007/programme.html")))
    ))

(define fortress-papers
   (list 
    (paper "The Fortress Language Specification"
           @list["Eric Allen" "David Chase" "Joe Hallett" "Victor Luchangco" "Jan-Willem Maessen" "Sukyoung Ryu" "Guy Steele"]
           "Sun Microsystems Technical Report, Version 1.0"
           "2008"
           `(("PDF" "http://labs.oracle.com/projects/plrg/fortress.pdf")))
    (paper "A Core Calculus of Metaclasses"
           @list["Eric Allen"]
           @a[href: "http://homepages.inf.ed.ac.uk/wadler/fool/"]{Workshop on Foundations of Object-Oriented Languages (FOOL)}
           "January 2005"
           `(("PDF" "http://research.sun.com/projects/plrg/fool2005.pdf")
             ("Proceedings" "http://homepages.inf.ed.ac.uk/wadler/fool/program/7.html")))))

(define analysis-papers
   (list 
    (preprint "Abstract Reduction Semantics for Modular Higher-Order Contract Verification"
              (list dvh)
              ""
              "July 2011"
              `(("PDF" "http://www.ccs.neu.edu/home/dvanhorn/pubs/tobin-hochstadt-vanhorn-preprint11.pdf")
                ("arXiv" "http://arxiv.org/abs/1103.1362")))
    (paper "Semantic Solutions to Program Analysis Problems"
           (list dvh)
           @a[href: "https://engineering.purdue.edu/~milind/pldi11fit/"]{Fun Ideas and Thoughts Session at the Conference on Programming Language Design and Implementation}
           "June 2011"
           `(["PDF" "http://www.ccs.neu.edu/home/dvanhorn/pubs/tobin-hochstadt-vanhorn-preprint11-2.pdf"]
             ["arXiv" "http://arxiv.org/abs/1105.0106"]))))
             

(define js-papers
   (list
    (preprint "Modules for JavaScript"
              (list dherman)
              ""
              "April 2011"
              `(["PDF" "js-modules.pdf"]))))

(define (format-title pr)
   (match pr
     [(abstract title _ _ _ _) (list title " (Abstract)")]
     [(preprint title _ _ _ _) (list title " (Preprint)")]
     [(paper title _ _ _ _) title]))

(define (format-paper pr)
   @p[class: 'pub]{
    @span[class: 'title (format-title pr)].
    @(format-coauthors (paper-co pr)) @~
    @(paper-loc pr)@(if (equal? "" (paper-loc pr)) "" ",") @(paper-date pr). @~
    @list["[ "]
    @(add-between 
        (for/list ([r (paper-resources pr)])
          @a[class: 'refType href: (second r) (first r)])
        " | ")
    @list[" ]"]
    })

(define (papers ps)
  @div{@h2[class: 'subproject]{Papers} @(map format-paper ps)})
