#lang scribble/html

@(require racket/list racket/match)

@(define sa string-append)
@(define ~ (br))

@(define sth "Sam Tobin-Hochstadt")

@(define (css url) @link[href: url rel: "stylesheet" type: "text/css"])
@(define (js . args) @script[type: "text/javascript" @(apply literal args) "\n"])

@(define (box id title . args)
   (apply div id: id class: "box" @h1[id: (if (eq? id 'name) 'topname "") class: 'boxtitle title]
          args))

@(define (project id title . body)
   (apply div id: id class: "project" @h1[class: 'projecttitle title]
          body))

@(define (pdesc . body)
   @p[class: 'projectdesc @(apply list body)])

@(struct paper (title co loc date resources))
@(struct abstract paper ())
@(struct preprint paper ())

@(struct talk (title url loc date where))

@(define MF @a[href: "http://www.ccs.neu.edu/home/matthias"]{Matthias Felleisen})
@(define mflatt @a[href: "http://www.cs.utah.edu/~mflatt"]{Matthew Flatt})
@(define stamourv @a[href: "http://www.ccs.neu.edu/home/stamourv"]{Vincent St-Amour})
@(define krhari @a[href: "http://www.ccs.neu.edu/home/krhari"]{Hari Prashanth K R})
@(define sstrickl @a[href: "http://www.ccs.neu.edu/home/sstrickl"]{T. Stephen Strickland})
@(define dherman @a[href: "http://www.ccs.neu.edu/home/dherman"]{Dave Herman})
@(define dvh @a[href: "http://www.ccs.neu.edu/home/dvanhorn"]{David Van Horn})
@(define rmc @a[href: "http://www.cs.utah.edu/~ryan"]{Ryan Culpepper})
@(define robby @a[href: "http://www.eecs.northwestern.edu/~robby"]{Robert Bruce Findler})
@(define chrdimo @a[href: "http://www.ccs.neu.edu/~chrdimo"]{Christos Dimoulas})
@(define cce @a[href: "http://www.ccs.neu.edu/~cce"]{Carl Eastlund})
@(define jay @a[href: "http://faculty.cs.byu.edu/~jay/home/"]{Jay McCarthy})
@(define jbc @a[href: "http://www.brinckerhoff.org/clements/"]{John Clements})

@(define (acm id)
   `("ACM DL"
     ,(string-append "http://portal.acm.org/citation.cfm?id=" id)))

@(define (neu id)
   `("PDF"
     ,(string-append "http://www.ccs.neu.edu/racket/pubs/" id ".pdf")))

@(define tr-papers
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

@(define macro-papers
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

@(define fortress-papers
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

@(define analysis-papers
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
             

@(define js-papers
   (list
    (preprint "Modules for JavaScript"
              (list dherman)
              ""
              "April 2011"
              `(["PDF" "js-modules.pdf"]))))

@(define analysis-talks
    (list
      (talk "Semantic Solutions to Program Analysis Problems"
            "fit11-talk.pdf"
            @a[href: "https://engineering.purdue.edu/~milind/pldi11fit/"]{Fun Ideas and Thoughts Session at the Conference on Programming Language Design and Implementation}
            "San Jose, CA" "June 2011")))

@(define js-talks
    (list
      (talk "The Future of the Web: It's coming!"
             #f
            "Childrens Hospital developers group"
            "Boston, MA" "December 2011")))


@(define macro-talks
   (list 
     (talk "Languages as Libraries"
               "pldi-2011.pdf"
           @a[href: "http://pldi11.cs.utah.edu/"]{Conference on Programming Language Design and Implementation (PLDI)}
               "San Jose, MA" "June 2011")

     (talk "Languages as Libraries"
               "mit-may-2011.pdf"
               @a[href: "http://www.csail.mit.edu/events/eventcalendar/calendar.php?show=event&id=2978"]{MIT
  CSAIL Programming Languages Working Group}
               "Cambridge, MA" "May 2011")
     (talk "Extensible Pattern Matching in an Extensible Language"
           "ifl2010-slides.pdf"
           @a[href: "http://www.cs.uu.nl/wiki/bin/view/IFL2010/WebHome"]{Implementation and Application of Functional Languages}
           "Alphen an der Rijn, Netherlands" "September 2010")
    ))

@(define tr-talks
   (list
    (talk "Growing Software: From Scripts to Programs"
          "osu-march-2011.pdf"
           @a[href: "http://eecs.oregonstate.edu/graduate/colloquium/"]{Oregon State University EECS Colloquium}
           "Corvallis, Oregon" "March 2011")
    (talk "From Scripts to Programs"
          #f
          "Indiana University Department of Computer Science"
          "Bloomington, IN" "November 2010")
    (talk "Logical Types for Untyped Languages"
          "icfp-2010-slides.pdf"
           @a[href: "http://www.icfpconference.org/icfp2010/index.html"]{International Conference on Functional Programming}
           "Baltimore, MD" "September 2010")
    (talk "Logical Types for Scheme"
          "nepls-2010-slides.pdf"
           @a[href: "http://nepls.org/Events/24/"]{New England Programming Languages and Systems Symposium}
           "Yale University" "April 2010")
    (talk "Typed Scheme: From Scripts to Programs"
          #f
          @span{@a[href: "http://www.eecs.harvard.edu/"]{Harvard University}}
           "Cambridge, MA" "February 2010")
    (talk "Types for Scheme, in Scheme" #f
             @a[href: "http://fare.livejournal.com/149685.html"]{Boston Lisp Meeting}
          "Boston, MA" "December 2009")
    (talk "Typed Scheme: From Scripts to Programs"
          "defense-slides.pdf"
           @span{Dissertation Defense, @a[href: "http://www.ccs.neu.edu/"]{Northeastern University}}
           "Boston, MA" "December 2009")
    (talk "Typed Scheme: From Scripts to Programs"
          #f
          "Sun Microsystems Laboratories"
          "Burlington, MA" "September 2009")
    (talk "The Design and Implementation of Typed Scheme"
          "mitchfest-slides.pdf"
          @a[href: "http://www.ccs.neu.edu/events/wand-symposium/"]{Symposium in
          Honor of Mitchell Wand}
          "Boston, MA" "August 2009")

    (talk "Cycles without pollution: a gradual typing poem"
          "stop09-slides.pdf"
          @a[href: "http://wrigstad.com/stop09/"]{1st International Workshop on Script to Program Evolution}
          "Genoa, Italy" "July 2009")

    (talk "To Type or Not To Type"
          #f
          @span{@a[href: "http://acm.ccs.neu.edu"]{Northeastern University ACM Speaker Series}}
           "Boston, MA" "April 2008")
    (talk "Typed Scheme"
          #f
          @span{@a[href: "http://www.ccs.neu.edu"]{Northeastern University CCIS Open House}}
           "Boston, MA" "March 2008")
    (talk "The Design and Implementation of Typed Scheme"
          #f
          @a[href: "http://www.cs.ucsd.edu/popl/08/"]{Symposium on Principles of Programming Languages (POPL)}
          "San Fransisco, CA" "January 2008")
    (talk "Types for Untyped Languages"
          #f
          @span{@a[href: "http://www.ccs.neu.edu"]{Northeastern University CCIS Open House}}
           "Boston, MA" "March 2007")
    (talk "Interlanguage Migration: From Scripts to Programs"
          "dls-slides.pdf"
          @a[href: "http://www.dcl.hpi.uni-potsdam.de/dls2006/openconf.php"]{Dynamic Languages Symposium (DLS)}
          "Portland, OR" "October 2006")
   ))


@(define (format-coauthors cos)
   (match cos
     [(list) null]
     [(list c) @span{With @|c|.}]
     [(list a ... b) @span{With @(add-between a ", ") and @|b|.}]))

@(define (format-title pr)
   (match pr
     [(abstract title _ _ _ _) (list title " (Abstract)")]
     [(preprint title _ _ _ _) (list title " (Preprint)")]
     [(paper title _ _ _ _) title]))

@(define (format-paper pr)
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

@(define (format-talk t)
  @p[class: 'pub]{
    @(if (talk-url t) @a[href: (talk-url t) class: 'talktitle (talk-title t)] (talk-title t)),
    @(list (talk-loc t) ", " (talk-date t) ", " (talk-where t) ".")})

@(define (papers ps)
   @div{@h2[class: 'subproject]{Papers} @(map format-paper ps)})

@(define (talks ps)
   @div{@h2[class: 'subproject]{Talks} @(map format-talk ps)})

@(define racket @a[href: "http://racket-lang.org"]{Racket})

@html{
 @head{
   @title[sth]
   @meta[name: "verify-v1" content: "1VWrH93RsveZVebOS9YtZ9P8a6r4e2syuwL80ueE4+0="]
   @meta[http-equiv: "Content-Type" content: "text/html" charset: "UTF-8"]
   @css{http://fonts.googleapis.com/css?family=Nobile}
   @css{style.css}
   @js{

  var _gaq = _gaq || [];
  _gaq.push(['_setAccount', 'UA-19575479-1']);
  _gaq.push(['_trackPageview']);

  (function() {
    var ga = document.createElement('script'); ga.type = 'text/javascript'; ga.async = true;
    ga.src = ('https:' == document.location.protocol ? 'https://ssl' : 'http://www') + '.google-analytics.com/ga.js';
    var s = document.getElementsByTagName('script')[0]; s.parentNode.insertBefore(ga, s);
  })();
}
 @js{
function toggleBibTeX(elt) {
    for (var pre = elt.parentNode.nextSibling;
         pre.tagName != "PRE";
         pre = pre.nextSibling);
    pre.style.display =
        (pre.style.display == "block") ? "none" : "block";
}}}

@body{

@div[id: 'sidebar]{
@div[id: 'sidebarcontent]{
@a[href: "#news"]{News}@~
@a[href: "#research"]{Research}@~
@a[href: "#teaching"]{Teaching}@~
@a[href: "#activities"]{Activities}@~
}}

@div[id: 'contents]{


@box['name sth]{
 @p{@img[id: "photo" src: "tree.jpg" alt: "Tree" title:"Winter"]
   @;@img[id: "photo" width: "200" src: "plt-logo-red-diffuse.png" alt: "Racket" title:"Racket"]
    @p{Research Assistant Professor @~
       @a[href: "http://www.ccs.neu.edu/racket/"]{PLT} @"@"
       @a[href: "http://www.ccs.neu.edu/research/prl/"]{Programming Research Lab}@~
       @a[href: "http://www.ccs.neu.edu/"]{College of Computer and Information Science}@~
       @a[href: "http://www.northeastern.edu/"]{Northeastern University}}}
 @p{Office: @a[href:"http://www.northeastern.edu/campusmap/"]{West Village H}, Room 358@~
    Email: @a[href:"mailto:samth@ccs.neu.edu" "samth@ccs.neu.edu"]@~
    Blog: @a[href:"http://scriptstoprograms.wordpress.com/" "Scripts to Programs"]@~
    Microblogging: @a[href: "http://twitter.com/samth/" "@samth"]@~
    Curriculum Vitae: @a[href: "cv.pdf"]{pdf}}
 @p{Papers: @a[href: "http://www.informatik.uni-trier.de/~ley/db/indices/a-tree/t/Tobin=Hochstadt:Sam.html"]{DBLP},
            @a[href: "http://scholar.google.com/citations?user=vMSSQbAAAAAJ"]{Google Scholar},
            @a[href: "http://arxiv.org/a/tobinhochstadt_s_1"]{arXiv},
            @a[href: "http://portal.acm.org/author_page.cfm?id=81319502825"]{ACM}}
 @p{Software: @a[href: "http://github.com/samth/"]{GitHub}}
 @p{Submit to @a[href: "http://www.dynamic-languages-symposium.org/"]{DLS 2012}!}
}
 
@box['news "News"]{
@p{The informal proceedings of STOP 2012 are now @a[href: "stop2012-proceedings.pdf"]{available}.}
@p{At @a[href: "http://splashcon.org/2011/"]{SPLASH}, I was interviewed by @a[href: "http://carmine.blogs.com/"]{Charles Torre} from @a[href: "http://channel9.msdn.com/"]{Microsoft Channel 9} about our design for @a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:modules"]{JavaScript modules}.  You can watch the video @a[href: "http://bit.ly/jsmodch9"]{here}.}
@p{I will be on the Program Committee for the @a[href: "http://www.icfpconference.org/icfp2012/index.html"]{International Conference on Functional Programming} in Copenhagen next year.}
@p{I've started blogging at 
@a[href: "http://scriptstoprograms.wordpress.com/"]{Scripts to Programs}.}
@p{Our @a[href: "http://eecs.northwestern.edu/~robby/lightweight-metatheory/"]{paper} on lightweight metatheory
    mechanization in @a[href: "http://redex.racket-lang.org"]{Redex} will appear at @a[href: "http://www.cse.psu.edu/popl/12/"]{POPL'12} in Philadelphia.}
 @p{Our @a[href: "http://www.ccs.neu.edu/racket/pubs/padl12-stff.pdf"]{paper} on Typed Racket's numeric tower 
        will appear at @a[href: "http://research.microsoft.com/en-us/um/people/crusso/padl12/"]{PADL'12} in Philadelphia.}
 @p{The @a[href: "http://ecoop12.cs.purdue.edu/content/script-program-evolution-stop"]{3rd International Workshop on Scripts to Programs} 
     will be co-located with ECOOP and PLDI in Beijing in June 2012.}}


@box['research "Research Projects"]{

@p{My research focuses on the design and implementation of programming
  systems.  I'm particularly interested in programming languages that
  support the evolution of software.  I'm currently working with the
 @a[href: "http://www.darpa.mil/Our_Work/I2O/Programs/Clean-slate_design_of_Resilient_Adaptive_Secure_Hosts_%28CRASH%29.aspx"]{DARPA CRASH} program on @a[href: "http://racket-lang.org"]{Racket} and with
@a[href: "https://mozillalabs.com/"]{Mozilla Labs} on @a[href: "http://ecmascript.org"]{JavaScript}.}

@project['typed "Typed Racket"]{
@pdesc{I created and
        maintain @a[href: "http://docs.racket-lang.org/ts-guide/"]{Typed
        Racket}, a statically-typed dialect
        of @racket that allows
        existing untyped Racket programs to be enriched with
      types.}
@(papers tr-papers)
@(talks tr-talks)
}

@project['metaprogramming "Building Languages"]{
      @pdesc{Developing @racket, I have helped to build a programmable
      programming language that allows developers to create
      custom languages for everything from pattern matching
      to type checking.}
@(papers macro-papers) @(talks macro-talks)}

@project['analysis "Analysis and Verification"]{
      @pdesc{I am developing  analysis and verification
      techniques for modular programs with rich specifications.}
       @(papers analysis-papers)
       @(talks analysis-talks)}


@project['javascript "JavaScript"]{
 @pdesc{In collaboration
      with @a[href:"https://mozillalabs.com/"]{Mozilla Research} and ECMA Technical Committee 39, I
      am working on the next version of the JavaScript language,
      focusing on making JavaScript an effective language for building
      large-scale web applications.}
  @(papers js-papers)
  @div{@h2[class: 'subproject]{Proposals}
  @p{@a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:modules"]{Modules} and
      @a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:module_loaders"]{Module Loaders}. 
      With @|dherman|.
     @~ Drafts from September 2011.}
  @p{@a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:private_name_objects"]{Private Names}. 
      With @dherman and Allen Wirfs-Brock.
     @~ Draft from September 2011.}
  }
 @(talks js-talks)}

@project['fortress "Fortress"]{
    @pdesc{@literal{In conjunction with
    the <a href="http://labs.oracle.com/projects/plrg/">Sun Labs
    Programming Language Research Group</a>, I helped to
    develop <a href="http://projectfortress.java.net/">Fortress</a>, a
    new language for high-performance, multicore and scientific
    computing.}}
     @(papers fortress-papers)
     }
}

@box['activities "Activities"]{
@p{@a[href: "http://www.icfpconference.org/icfp2012/index.html"]{ICFP 2012}, Program Committee}
@p{@a[href: "http://wrigstad.com/stop/"]{STOP 2012}, Chair}
@p{@a[href: "http://scheme2011.ucombinator.org/"]{Scheme Workshop 2011}, Program Committee}
@p{@a[href: "http://nepls.org/Events/25"]{NEPLS 25}, Chair}
@p{@a[href: "http://www.mpi-sws.org/~dreyer/tldi2011/"]{TLDI 2011}, Program Committee}
@p{@a[href: #f]{FOOL 2010}, Program Committee}
@p{@a[href: #f]{TFP 2010}, Program Committee}
}

@box['teaching "Teaching"]{ 
@p{ In Spring 2011, I taught a new honors section of
@a[href: "http://www.ccs.neu.edu/course/cs2510h/"]{CS 2510} with
@a[href: "http://www.ccs.neu.edu/home/dvanhorn/"]{David Van Horn}.}

@p{ In Spring 2009, I taught @a[href: "211-09/"]{CS U211}.  }

@p{ In Fall 2005, I taught CS U213.}}

@;@box['software "Software"]{}

@box['life "Personal"]{
@p{
  In the rest of my life, I play @a[href:"http://www.upa.org/"]{Ultimate} and I 
@a[href:"http://www.outdoors.org"]{go outside}.  }

@p{My wife, Katie Edmonds, is a graduate student in the 
@a[href:"http://gwagner.med.harvard.edu/"]{Wagner lab} at the Harvard Medical School.}}



@; the end
}
}}