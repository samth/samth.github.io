#lang at-exp racket

(provide (all-defined-out))
(require scribble/html "people.rkt" "utils.rkt")

@(define oopsla-12
   @a[href: "http://splashcon.org/2012/"]{Object Oriented Programming, Systems, Languages and Applications (OOPSLA)})

@(define esop-13
   @a[href: "http://www.ccs.neu.edu/esop2013/"]{European Symposium on Programming (ESOP)})

@(define esop-14
   @a[href: "http://flint.cs.yale.edu/esop2014/"]{European Symposium on Programming (ESOP)})

@(define (acm id)
   `("ACM DL"
     ,(string-append "http://portal.acm.org/citation.cfm?id=" id)))

@(define (neu id)
   `("PDF"
     ,(string-append "http://www.ccs.neu.edu/racket/pubs/" id ".pdf")))

(struct paper (title co loc date resources tag))
(struct abstract paper ())
(struct preprint paper ())

(define-syntax-rule (defpapers id [p ...] ...)
  (define id
    (list (mk-paper p ...) ...)))

(define (mk-paper title co loc date resources #:type [type 'paper] #:tag [tag #f])
  ((case type
     [(paper) paper]
     [(preprint) preprint]
     [(abstract) abstract])
   title co loc date resources tag))

(defpapers tr-papers
  ("Constraining Delimited Control with Contracts"
   (list asumu sstrickl)
   esop-13
   "March 2013"
   (list (neu "esop13-tsth"))
   #:tag 'cont)

  ("Gradual Typing for First-class Classes"
   (list asumu sstrickl chrdimo MF)
   oopsla-12
   "October 2012"
   (list (neu "oopsla12-tsdthf"))
   #:tag 'fcc)

  ("Proceedings of the Third Workshop on Script to Program Evolution"
   (list)
   "NU CCIS Technical Report NU-CCIS-12-02"
   "June 2012"
   `(("PDF" "stop2012-proceedings.pdf")))

  ("Complete Monitors for Behavioral Contracts"
   (list chrdimo MF)
   "European Symposium on Programming (ESOP)"
   "March 2012"
   `(,(neu "esop12-dthf")))

  ("Typing the Numeric Tower"
   (list stamourv mflatt MF)
   @a[href: "http://research.microsoft.com/en-us/um/people/crusso/padl12/"]{Symposium on Practical Aspects of Declarative Languages (PADL)}
   "January 2012"
   `(,(neu "padl12-stff")))

  ("Logical Types for Untyped Languages"
   (list MF)
   @a[href: "http://www.icfpconference.org/icfp2010/index.html"]{International Conference on Functional Programming (ICFP)}
   "September 2010"
   `(,(neu "icfp10-thf") ,(acm "1863561")))

  ("The Design and Implementation of Typed Scheme"
   (list MF)
   @span{Accepted for publication in @a[href: "http://www.brics.dk/~hosc/"]{Higher-Order and Symbolic Computation}}
   "September 2010"
   `(("PDF" "refinement-mitchfest.pdf")
     ("arXiv" "http://arxiv.org/abs/1106.2575"))
   #:type 'preprint)

  ("Functional Data Structures for Typed Racket"
   (list krhari)
   @a[href: "http://www.iro.umontreal.ca/~sfp2010/"]{Workshop on Scheme and Functional Programming}
   "August 2010"
   `(,(neu "sfp10-kth")
     ("PLaneT Package" "http://planet.racket-lang.org/display.ss?package=pfds.plt&owner=krhari")))

  ("Typed Scheme: From Scripts to Programs"
   null
   "PhD Dissertation, Northeastern University"
   "January 2010"
   `(,(neu "dissertation-tobin-hochstadt")
     #;("ProQuest" "")))

  ("Cycles without pollution: a gradual typing poem"
   (list robby)
   @a[href: "http://wrigstad.com/stop09/"]{1st International Workshop on Script to Program Evolution (STOP)}
   "July 2009"
   `(,(neu "stop09-ft")
     ,(acm "1570506.1570512")))

  ("Practical Variable-Arity Polymorphism"
   (list sstrickl MF)
   @a[href: "http://esop09.pps.jussieu.fr/"]{European Symposium on Programming (ESOP)}
   "March 2009"
   `(,(neu "esop09-sthf")
     ("Springer" "http://www.springerlink.com/content/x4l6q4n112425081/")))

  ("The Design and Implementation of Typed Scheme"
   (list MF)
   @a[href: "http://www.cs.ucsd.edu/popl/08/"]{Symposium on Principles of Programming Languages (POPL)}
   "January 2008"
   `(,(neu "popl08-thf") 
     ,(acm "1328486")
     ("Formal Models" "https://github.com/samth/popl08-model")))

  ("Interlanguage Migration: From Scripts to Programs"
   (list MF)
   @a[href: "http://www.dcl.hpi.uni-potsdam.de/dls2006/openconf.php"]{Dynamic Languages Symposium (DLS)}
   "October 2006"
   `(,(neu "dls06-tf") 
     ,(acm "1176617.1176755")))
  )

(defpapers macro-papers
    ("Meta-tracing makes a fast Racket"
     (list cfbolz krono jseik)
     "Workshop on Dynamic Languages and Applications (DYLA)"
     "June 2014"
     `(("PDF" "pycket-dyla.pdf")
       ("GitHub" "https://github.com/samth/pycket"))
     #:tag 'pycket-dyla)

    ("Taming the Parallel Effect Zoo: Extensible Deterministic Parallelism with LVish"
     (list lkuper atodd rrnewton)
     "Conference on Programming Languages Design and Implementation (PLDI)"
     "June 2014"
     `(("PDF" "effectzoo-pldi14.pdf")
       ("LVish" "https://hackage.haskell.org/package/lvish"))
     #:tag 'effectzoo)

    ("The Network as a Language Construct"
     (list tonyg MF)
     esop-14
     "April 2014"
     `(("PDF" "http://www.ccs.neu.edu/racket/pubs/esop14-gjthf.pdf")
       ("Web Page" "http://www.ccs.neu.edu/home/tonyg/esop2014/")
       ("Marketplace" "http://tonyg.github.io/marketplace/"))
     #:tag 'network-calc)
    ("Chaperones and Impersonators: Runtime support for reasonable interposition"
     (list sstrickl robby mflatt)
     oopsla-12
     "October 2012"
     (list (neu "oopsla12-sthff")
           '("Web Page" "http://sstrickl.net/chaperones/")
           '("Documentation" "http://docs.racket-lang.org/reference/chaperones.html"))
     #:tag 'chaperones)
    ("Optimization Coaching"
     (list stamourv MF)
     oopsla-12
     "October 2012"
     (list (neu "oopsla12-stf")
           '("GitHub" "https://github.com/stamourv/optimization-coach"))
     #:tag 'opt-coach)
    ("Run Your Research: On the Effectiveness of Lightweight Mechanization"
     (list "Casey Klein" jbc chrdimo cce MF mflatt jay "Jon Rafkind" robby)
     @a[href: "http://www.cse.psu.edu/popl/12/"]{Symposium on Principles of Programming Languages (POPL)}
     "January 2012"
     `(("PDF" "http://eecs.northwestern.edu/~robby/lightweight-metatheory/popl2012-kcdeffmrtf.pdf")
       ("Models" "http://eecs.northwestern.edu/~robby/lightweight-metatheory/")
       ("Redex" "http://redex.racket-lang.org/")))
    ("Languages as Libraries"
     (list stamourv rmc mflatt MF)
     @a[href: "http://pldi11.cs.utah.edu/"]{Conference on Programming Language Design and Implementation (PLDI)}
     "June 2011"
     `(,(neu "pldi11-thacff")
       ,(acm "1993514")))
    ("Extensible Pattern Matching in an Extensible Language"
     null
     ""
     "October 2010"
     `(("PDF" "match-ifl-full.pdf")
       ("arXiv" "http://arxiv.org/abs/1106.2578")
       ("Documentation" "http://docs.racket-lang.org/reference/match.html"))
     #:type 'preprint)
    ("Extensible Pattern Matching in an Extensible Language"
     null
     @a[href: "http://www.cs.uu.nl/wiki/bin/view/IFL2010/WebHome"]{Symposium on Implementation and Application of Functional Languages}
     "September 2010"
     `(("PDF" "ifl-2010-abstract.pdf")
       ("Utrecht Technical Report" "http://www.cs.uu.nl/research/techreps/UU-CS-2010-020.html"))
     #:type 'abstract)
    ("Where are you going with those types?"
     (list stamourv mflatt MF)
     @a[href: "http://www.cs.uu.nl/wiki/bin/view/IFL2010/WebHome"]{Symposium on Implementation and Application of Functional Languages}
     "September 2010"
     `(("PDF" "http://www.ccs.neu.edu/home/stamourv/ifl10.pdf")                
       ("Utrecht Technical Report" "http://www.cs.uu.nl/research/techreps/UU-CS-2010-020.html"))
     #:type 'abstract)
    
    ("Advanced Macrology and the Implementation of Typed Scheme"
     (list rmc mflatt)
     @a[href: "http://www.schemeworkshop.org/2007/"]{Workshop on Scheme and Functional Programming}
     "September 2007"
     `(,(neu "scheme2007-cft")
       ("Proceedings" "http://www.schemeworkshop.org/2007/programme.html")))
    )

(defpapers fortress-papers
  ("The Fortress Language Specification"
   @list["Eric Allen" "David Chase" "Joe Hallett" "Victor Luchangco" "Jan-Willem Maessen" "Sukyoung Ryu" "Guy Steele"]
   "Sun Microsystems Technical Report, Version 1.0"
   "2008"
   `(("PDF" "fortress-spec.pdf")))

  ("A Core Calculus of Metaclasses"
   @list["Eric Allen"]
   @a[href: "http://homepages.inf.ed.ac.uk/wadler/fool/"]{Workshop on Foundations of Object-Oriented Languages (FOOL)}
   "January 2005"
   `(("PDF" "fool05-tha.pdf")
     ("Proceedings" "http://homepages.inf.ed.ac.uk/wadler/fool/program/7.html"))))

(defpapers analysis-papers
  ("Higher-order Symbolic Execution via Contracts"
   (list dvh)
   oopsla-12
   "October 2012"
   (list (neu "oopsla12-thvh")
	 '("arXiv" "http://arxiv.org/abs/1103.1362"))
   #:tag 'symexp)

  ("Semantic Solutions to Program Analysis Problems"
   (list dvh)
   @a[href: "https://engineering.purdue.edu/~milind/pldi11fit/"]{Fun Ideas and Thoughts Session at the Conference on Programming Language Design and Implementation}
   "June 2011"
   `(["PDF" "http://www.ccs.neu.edu/home/dvanhorn/pubs/tobin-hochstadt-vanhorn-preprint11-2.pdf"]
     ["arXiv" "http://arxiv.org/abs/1105.0106"])))
             

(defpapers js-papers
  ("Modules for JavaScript"
   (list dherman)
   ""
   "April 2011"
   `(["PDF" "js-modules.pdf"])
   #:type 'preprint))

(defpapers edu-papers
  ("From Principles to Practice with Class in the First Year"
   (list dvh)
   "Trends in Functional Programming in Education"
   "May 2013"
   `(("PDF" "tfpie.pdf"))
   #:tag "tfpie13"))

(define (format-title pr)
   (match pr
     [(abstract title _ _ _ _ _) (list title " (Abstract)")]
     [(preprint title _ _ _ _ _) (list title " (Preprint)")]
     [(paper title _ _ _ _ _) title]))

(define (format-paper pr)
  (define title 
    (if (paper-tag pr)
        (a class: 'title name: (paper-tag pr) (format-title pr))
        (format-title pr)))
  (define pub
    @p[class: 'pub]{
      @span[class: 'title title].
	   @(format-coauthors (paper-co pr)) @~
	   @(paper-loc pr)@(if (equal? "" (paper-loc pr)) "" ",") @(paper-date pr). 
	   @~
	   @span[class: 'paper-resource]{
	      @list["[ "]
	      @(add-between 
		(for/list ([r (paper-resources pr)])
			  @a[class: 'refType href: (second r) (first r)])
		" | ")
	      @list[" ]"]}})

  pub)

(define (papers ps)
  @div{@h2[class: 'subproject]{Papers} @(map format-paper ps)})
