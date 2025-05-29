#lang at-exp racket

(provide (all-defined-out))
(require scribble/html "people.rkt" "utils.rkt")

@(define snapl-15
   @a[href: "http://snapl.org/2015/index.html"]{Summit on Advances in Programming Languages (SNAPL)})

@(define oopsla-12
   @a[href: "http://splashcon.org/2012/"]{Object Oriented Programming, Systems, Languages and Applications (OOPSLA)})

@(define icfp-14
   @a[href: "http://icfpconference.org/2014/"]{International Conference on Functional Programming (ICFP)})

@(define ECOOP "European Conference on Object-Oriented Programming (ECOOP)")
@(define ecoop-15 @a[href: "http://2015.ecoop.org" ECOOP])

@(define ESOP "European Symposium on Programming (ESOP)")
@(define esop-15 @a[href: "http://conf.researchr.org/home/esop-2015" ESOP])

@(define esop-13 @a[href: "http://www.ccs.neu.edu/esop2013/" ESOP])

@(define esop-14 @a[href: "http://flint.cs.yale.edu/esop2014/" ESOP])

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
  ("Corpse reviver: sound and efficient gradual typing via contract verification"
   (list cameron-moy phuc dvh)
   @a[href: "https://popl21.sigplan.org/"]{Symposium on Principles of Programming Languages (POPL)}
   "January 2021"
   (list '("ACM" "https://doi.org/10.1145/3434334")
         '("arXiv" "http://arxiv.org/abs/2007.12630"))
   #:tag 'corpse-reviver)

  ("Sound gradual typing: only mostly dead"
   (list "Spenser Bauman" cfbolz jsiek)
   @a[href: "https://2017.splashcon.org/track/splash-2017-OOPSLA"]{Object Oriented Programming, Systems, Languages and Applications (OOPSLA)}
   "October 2017"
   (list '("ACM" "https://doi.org/10.1145/3133878"))
   #:tag 'gradual-typing-dead)

  ("Migratory Typing: Ten Years Later"
   (list MF robby mflatt bgreenman akent stamourv sstrickl asumu)
   @a[href: "https://snapl.org/2017/"]{Summit on Advances in Programming Languages (SNAPL)}
   "May 2017"
   (list '("ACM" "https://doi.org/10.4230/LIPIcs.SNAPL.2017.17"))
   #:tag 'migratory-typing)

  ("Occurrence typing modulo theories"
   (list akent "David Kempe")
   @a[href: "https://pldi16.sigplan.org/"]{Conference on Programming Language Design and Implementation (PLDI)}
   "June 2016"
   (list '("ACM" "https://doi.org/10.1145/2908080.2908091"))
   #:tag 'occurrence-typing)

  ("Practical Optional Types for Clojure"
   (list ambrose rowan-davies)
   @a[href: "https://www.etaps.org/2016/esop"]{European Symposium on Programming (ESOP)}
   "April 2016"
   (list '("Springer" "https://doi.org/10.1007/978-3-662-49498-1_4"))
   #:tag 'clojure-types)

  ("The Recursive Union of Some Gradual Types"
   (list jsiek)
   "A List of Successes That Can Change the World - Essays Dedicated to Philip Wadler"
   "2016"
   (list '("Springer" "https://doi.org/10.1007/978-3-319-30936-1_21"))
   #:tag 'recursive-union)

  ("Towards Practical Gradual Typing"
   (list asumu "Daniel Feltey" "Earl Dean" mflatt robby MF)
   ecoop-15
   "July 2015"
   (list (neu "ecoop2015-takikawa-et-al")
         '("Artifact" "http://www.ccs.neu.edu/home/racket/ecoop2015/")
         '("Documentation" "http://docs.racket-lang.org/ts-reference/Typed_Classes.html"))
   #:tag 'ecoop15)

  ("Monotonic References for Efficient Gradual Typing"
   (list jsiek vitousek matteo rxg)
   esop-15
   "April 2015"
   (list '("PDF" "https://dl.dropboxusercontent.com/u/10275252/monotonic-references.pdf"))
   #:tag 'esop15)

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
     ,(acm "1176617.1176755")))    )

(defpapers dsl-papers
  ("Rhombus: A New Spin on Macros without All the Parentheses"
   (list mflatt "Taylor Allred" "Nia Angle" "Stephen De Gabrielle" robby "Jack Firth" "Kiran Gopinathan" bgreenman "Siddhartha Kasivajhula" "Alex Knauth" jay "Sam Phillips" "Sorawee Porncharoenwase" "Jens Axel Søgaard")
   @a[href: "https://2023.splashcon.org/track/splash-2023-oopsla"]{Object Oriented Programming, Systems, Languages and Applications (OOPSLA)}
   "October 2023"
   (list '("ACM" "https://doi.org/10.1145/3622818"))
   #:tag 'rhombus)

  ("Sham: A DSL for Fast DSLs"
   (list rajan-walia chung-chieh-shan)
   "Art, Science, and Engineering of Programming"
   "2022"
   (list '("Journal" "https://doi.org/10.22152/programming-journal.org/2022/6/4")
         '("arXiv" "https://arxiv.org/abs/2005.09028"))
   #:tag 'sham)

  ("Forward build systems, formally"
   (list spall neil-mitchell)
   @a[href: "https://popl22.sigplan.org/home/CPP-2022"]{Certified Programs and Proofs (CPP)}
   "January 2022"
   (list '("ACM" "https://doi.org/10.1145/3497775.3503687")
         '("arXiv" "https://arxiv.org/abs/2202.05328"))
   #:tag 'forward-builds)

  ("Build scripts with perfect dependencies"
   (list spall neil-mitchell)
   @a[href: "https://2020.splashcon.org/track/splash-2020-oopsla"]{Object Oriented Programming, Systems, Languages and Applications (OOPSLA)}
   "November 2020"
   (list '("ACM" "https://doi.org/10.1145/3428237")
         '("arXiv" "https://arxiv.org/abs/2007.12737"))
   #:tag 'perfect-deps)

  ("From high-level inference algorithms to efficient code"
   (list rajan-walia praveen-narayanan jacques-carette chung-chieh-shan)
   @a[href: "https://icfp19.sigplan.org/"]{International Conference on Functional Programming (ICFP)}
   "August 2019"
   (list '("ACM" "https://doi.org/10.1145/3341702"))
   #:tag 'inference-algorithms)

  ("Rebuilding racket on chez scheme (experience report)"
   (list mflatt "Caner Derici" "R. Kent Dybvig" "Andrew W. Keep" "Gustavo E. Massaccesi" spall "Jon Zeppieri")
   @a[href: "https://icfp19.sigplan.org/"]{International Conference on Functional Programming (ICFP)}
   "August 2019"
   (list '("ACM" "https://doi.org/10.1145/3341642"))
   #:tag 'racket-chez)

  ("A programmable programming language"
   (list MF robby mflatt sk eli jay)
   "Communications of the ACM"
   "March 2018"
   (list '("ACM" "https://doi.org/10.1145/3127323"))
   #:tag 'programmable-lang)

  ("Compiling Tree Transforms to Operate on Packed Representations"
   (list michael-vollmer spall "Buddhika Chamith" "Laith Sakka" chaitanya "Milind Kulkarni" rrnewton)
   @a[href: "https://2017.ecoop.org/"]{European Conference on Object-Oriented Programming (ECOOP)}
   "June 2017"
   (list '("ACM" "https://doi.org/10.4230/LIPIcs.ECOOP.2017.26"))
   #:tag 'tree-transforms)

  ("The Racket Manifesto"
   (list MF robby mflatt sk eli jay)
   snapl-15
   "May 2015"
   (list (neu "manifesto")
         '("HTML" "http://www.ccs.neu.edu/home/matthias/manifesto/"))
   #:tag 'manifesto)
  
  ("Meta-tracing makes a fast Racket"
   (list cfbolz krono jsiek)
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

(defpapers verification-papers
  ("Type Checking Extracted Methods"
   (list yuquan-fu)
   "Art, Science, and Engineering of Programming"
   "2022"
   (list '("Journal" "https://doi.org/10.22152/programming-journal.org/2022/6/6")
         '("arXiv" "https://arxiv.org/abs/2010.03608"))
   #:tag 'type-checking-extracted)
  )

(defpapers systems-papers
  ("Garbage Collection for Mostly Serialized Heaps"
   (list chaitanya "Vidush Singhal" "Aditya Gupta" "Mike Rainey" michael-vollmer "Artem Pelenitsyn" "Milind Kulkarni" rrnewton)
   @a[href: "https://ismm24.sigplan.org/"]{International Symposium on Memory Management (ISMM)}
   "June 2024"
   (list '("ACM" "https://doi.org/10.1145/3652024.3665512"))
   #:tag 'gc-serialized)

  ("Parallel type-checking with haskell using saturating LVars and stream generators"
   (list rrnewton "Ömer S. Ağacan" "Peter P. Fogg")
   @a[href: "https://ppopp16.sigplan.org/"]{Symposium on Principles and Practice of Parallel Programming (PPoPP)}
   "March 2016"
   (list '("ACM" "https://doi.org/10.1145/2851141.2851142"))
   #:tag 'parallel-typing)
  )

(defpapers fortress-papers
  ("The Fortress Language Specification"
   @list["Eric Allen" "David Chase" "Joe Hallett" "Victor Luchangco" "Jan-Willem Maessen" "Suky
oung Ryu" "Guy Steele"]
   "Sun Microsystems Technical Report, Version 1.0"
   "2008"
   `(("PDF" "fortress-spec.pdf")))

  ("A Core Calculus of Metaclasses"
   @list["Eric Allen"]
   @a[href: "http://homepages.inf.ed.ac.uk/wadler/fool/"]{Workshop on Foundations of Object-Ori
ented Languages (FOOL)}
   "January 2005"
   `(("PDF" "fool05-tha.pdf")
     ("Proceedings" "http://homepages.inf.ed.ac.uk/wadler/fool/program/7.html"))))

(defpapers analysis-papers
  ("Size-change termination as a contract: dynamically and statically enforcing termination for higher-order programs"
   (list phuc thomas-gilray dvh)
   @a[href: "https://pldi19.sigplan.org/"]{Conference on Programming Language Design and Implementation (PLDI)}
   "June 2019"
   (list '("ACM" "https://doi.org/10.1145/3314221.3314643"))
   #:tag 'size-change-contract)

  ("Soft contract verification for higher-order stateful programs"
   (list phuc thomas-gilray dvh)
   @a[href: "https://popl18.sigplan.org/"]{Symposium on Principles of Programming Languages (POPL)}
   "January 2018"
   (list '("ACM" "https://doi.org/10.1145/3158139"))
   #:tag 'soft-contract-stateful)

  ("Higher order symbolic execution for contract verification and refutation"
   (list phuc dvh)
   "Journal of Functional Programming"
   "2017"
   (list '("Cambridge" "https://doi.org/10.1017/S0956796816000216"))
   #:tag 'higher-order-symbolic)

  ("Soft Contract Verification"
   (list "Phil Nguyen" dvh)
   icfp-14
   "September 2014"
   (list '("ACM" "http://dl.acm.org/authorize?N83790")
     '("arXiv" "http://arxiv.org/abs/1307.6239"))
   #:tag 'scv)

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
