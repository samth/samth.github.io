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

@(define MF @a[href: "http://www.ccs.neu.edu/home/matthias"]{Matthias Felleisen})
@(define mflatt @a[href: "http://www.cs.utah.edu/~mflatt"]{Matthew Flatt})
@(define stamourv @a[href: "http://www.ccs.neu.edu/home/stamourv"]{Vincent St-Amour})
@(define krhari @a[href: "http://www.ccs.neu.edu/home/krhari"]{Hari Prashanth K R})
@(define sstrickl @a[href: "http://www.ccs.neu.edu/home/sstrickl"]{T. Stephen Strickland})
@(define dherman @a[href: "http://www.ccs.neu.edu/home/dherman"]{Dave Herman})
@(define dvh @a[href: "http://www.ccs.neu.edu/home/dvanhorn"]{David Van Horn})
@(define rmc @a[href: "http://www.cs.utah.edu/~ryan"]{Ryan Culpepper})
@(define robby @a[href: "http://www.eecs.northwestern.edu/~robby"]{Robert Bruce Findler})

@(define (acm id)
   `("ACM DL"
     ,(string-append "http://portal.acm.org/citation.cfm?id=" id)))

@(define (neu id)
   `("PDF"
     ,(string-append "http://www.ccs.neu.edu/scheme/pubs/" id ".pdf")))

@(define tr-papers
   (list 
    (paper "Logical Types for Untyped Languages"
           (list MF)
           @a[href: "http://www.icfpconference.org/icfp2010/index.html"]{International Conference on Functional Programming (ICFP)}
           "September 2010"
           `(,(neu "icfp10-thf") ,(acm "1863561")))
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
             ("Isabelle Model" "TypedScheme.thy")
             ("Redex Model" "ts-redex.tgz")))
    (paper "Interlanguage Migration: From Scripts to Programs"
           (list MF)
           @a[href: "http://www.dcl.hpi.uni-potsdam.de/dls2006/openconf.php"]{Dynamic Languages Symposium (DLS)}
           "October 2006"
           `(,(neu "dls06-thf") 
             ,(acm "1176617.1176755")))
    ))

@(define macro-papers
   (list
    (paper "Languages as Libraries"
           (list stamourv rmc mflatt MF)
           @a[href: "http://pldi11.cs.utah.edu/"]{PLDI}
           "June 2011"
           `(,(neu "pldi11-thacff")))
    (abstract "Extensible Pattern Matching in an Extensible Language"
              null
              @a[href: "http://www.cs.uu.nl/wiki/bin/view/IFL2010/WebHome"]{Symposium on Implementation and Application of Functional Languages}
              "September 2010"
              `(("PDF" "ifl-2010-abstract.pdf")))
    (abstract "Where are you going with those types?"
              (list stamourv mflatt MF)
              @a[href: "http://www.cs.uu.nl/wiki/bin/view/IFL2010/WebHome"]{Symposium on Implementation and Application of Functional Languages}
              "September 2010"
              `(("PDF" "http://www.ccs.neu.edu/home/stamourv/ifl10.pdf")))
    (paper "Advanced Macrology and the Implementation of Typed Scheme"
           (list rmc mflatt)
           @a[href: "http://www.schemeworkshop.org/2007/"]{Workshop on Scheme and Functional Programming}
           "September 2007"
           `(,(neu "scheme2007-cft")))
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
           `(("PDF" "http://research.sun.com/projects/plrg/fool2005.pdf")))))

@(define analysis-papers
   (list 
    (paper "Semantic Solutions to Program Analysis Problem"
           (list dvh)
           @a[href: "https://engineering.purdue.edu/~milind/pldi11fit/"]{Fun Ideas and Thoughts Session at the Conference on Programming Language Design and Implementation}
           "June 2011"
           `(["PDF" "http://www.ccs.neu.edu/home/dvanhorn/pubs/tobin-hochstadt-vanhorn-preprint11-2.pdf"]
             ["arXiv" "http://arxiv.org/abs/1105.0106"]))
    (preprint "Modular Analysis via Abstract Reduction Semantics"
              (list dvh)
              ""
              "March 2011"
              `(("PDF" "http://www.ccs.neu.edu/home/dvanhorn/pubs/tobin-hochstadt-vanhorn-preprint11.pdf")
                ("arXiv" "http://arxiv.org/abs/1103.1362")))))

@(define js-papers
   (list
    (preprint "Modules for JavaScript"
              (list dherman)
              ""
              "April 2011"
              `(["PDF" "js-modules.pdf"]))))


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
    @(paper-loc pr) @(if (equal? "" (paper-loc pr)) "" ",") @(paper-date pr). @~
    @list["[ "]
    @(add-between 
        (for/list ([r (paper-resources pr)])
          @a[class: 'refType href: (second r) (first r)])
        " | ")
    @list[" ]"]
    })

@(define (papers ps)
   @div{@h2[class: 'subproject]{Papers} @(map format-paper ps)})

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
@div[id: 'contents]{

@box['name sth]{
 @p{@img[id: "photo" src: "tree.jpg" alt: "Tree" title:"Winter"]
    @p{@a[href: "https://mozillalabs.com/"]{Mozilla Research Fellow} @~
       @a[href: "http://www.ccs.neu.edu/scheme/"]{PLT} @quote["@"]
       @a[href: "http://www.ccs.neu.edu/research/prl/"]{Programming Research Lab}@~
       @a[href: "http://www.ccs.neu.edu/"]{College of Computer and Information Science}@~
       @a[href: "http://www.northeastern.edu/"]{Northeastern University}}}
 @p{Office: @a[href:"http://www.northeastern.edu/campusmap/"]{West Village H}, Room 308@~
    Email: @a[href:"mailto:samth@ccs.neu.edu" "samth@ccs.neu.edu"]@~}}

@box['research "Research Projects"]{

@p{My research focuses on the design and implementation of programming
  systems.  I'm particularly interested in programming languages that
  support the evolution of software.}

@project['typed "Typed Racket"]{
@pdesc{I created and
        maintain @a[href: "http://docs.racket-lang.org/ts-guide/"]{Typed
        Racket}, a statically-typed dialect
        of @racket that allows
        existing untyped Racket programs to be enriched with
      types.}
@(papers tr-papers)
}

@project['metaprogramming "Building Languages"]{
      @pdesc{Developing @racket, I have helped to build a programmable
      programming language that allows developers to create
      custom languages for everything from pattern matching
      to type checking.}
@(papers macro-papers)}

@project['analysis "Analysis and Verification"]{
      @pdesc{I am developing  analysis and verification
      techniques for modular programs with rich specifications.}
       @(papers analysis-papers)}

@project['javascript "JavaScript"]{
 @pdesc{In collaboration
      with @a[href:"https://mozillalabs.com/"]{Mozilla Research}, I
      am working on the next version of the JavaScript language,
      focusing on making JavaScript an effective language for building
      large-scale web applications.}
  @(papers js-papers)
  @div{@h2[class: 'subproject]{Proposals}
  @p{@a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:modules"]{Modules} and
      @a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:module_loaders"]{Module Loaders}. 
      With @|dherman|.
     @~ Drafts from March 2011.}
  @p{@a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:private_names"]{Private Names}. 
      With @dherman and Allen Wirfs-Brock.
     @~ Draft from March 2011.}
  }}

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
}}}
