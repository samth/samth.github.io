#lang scribble/html

@(require racket/list racket/match "utils.rkt"
	  "people.rkt" "papers.rkt" "talks.rkt")

@(define (css url) @link[href: url rel: "stylesheet" type: "text/css"])
@(define (js . args) @script[type: "text/javascript" @(apply literal args) "\n"])

@(define (box id title . args)
   (apply div id: id class: "box" @h1[id: (if (eq? id 'name) 'topname "")
                                      class: 'boxtitle title]
          args))

@(define (project id title . body)
   (apply div id: id class: "project" @h1[class: 'projecttitle title]
          body))

@(define (pdesc . body)
   @p[class: 'projectdesc @(apply list body)])

@(define toggle-bibtex
   @js{
function toggleBibTeX(elt) {
    for (var pre = elt.parentNode.nextSibling;
         pre.tagName != "PRE";
         pre = pre.nextSibling);
    pre.style.display =
        (pre.style.display == "block") ? "none" : "block";
}})

@(define analytics
   @js{

  var _gaq = _gaq || [];
  _gaq.push(['_setAccount', 'UA-19575479-1']);
  _gaq.push(['_trackPageview']);

  (function() {
    var ga = document.createElement('script'); ga.type = 'text/javascript'; ga.async = true;
    ga.src = ('https:' == document.location.protocol ? 'https://ssl' : 'http://www') + '.google-analytics.com/ga.js';
    var s = document.getElementsByTagName('script')[0]; s.parentNode.insertBefore(ga, s);
  })();
})


@(define sidebar
@div[id: 'sidebar]{
@div[id: 'sidebarcontent]{
@h1{@a[href: "#news"]{News}}@~
@h1{@a[href: "#research"]{Research}}@~
@h1{@a[href: "#activities"]{Activities}}@~
@h1{@a[href: "#teaching"]{Teaching}}@~
}})

@(define racket @a[href: "http://racket-lang.org"]{Racket})

@html{
 @head{
   @title[sth]
   @meta[name: "verify-v1"
	 content: "1VWrH93RsveZVebOS9YtZ9P8a6r4e2syuwL80ueE4+0="]
   @meta[http-equiv: "Content-Type" content: "text/html" charset: "UTF-8"]
   @css{http://fonts.googleapis.com/css?family=PT+Sans}
   @css{http://fonts.googleapis.com/css?family=Paprika}
   @css{http://fonts.googleapis.com/css?family=Nobile}
   @css{style.css}
   @|analytics|
   }

@body{

@|sidebar|

@div[id: 'contents]{

             @; @p{Programming language semanticists should be the obstetricians of programming languages, not their coroners.
@; @|~| @div[id: "nameright"]{- John C. Reynolds}}}}}


@box['name sth]{
@div[class: "right"]{
      @p{@img[id: "photo" src: "tree.jpg" alt: "Tree" title:"Winter"]}
      @div{@p[style: "font-size: 85%;"]{@i{The most important decisions a scholar makes are what problems to work on.}  - @a[href: "http://www.tobinproject.org/about/james-tobin"]{James Tobin}}}}
 @div{

    @p{Assistant Professor @~
       @a[href: "http://racket-lang.org/people.html"]{PLT} &
        @a[href: "http://wonks.github.io"]{PL} @"@"
       @a[href: "http://www.soic.indiana.edu/"]{School of Informatics & Computing}@~
       @a[href: "http://www.indiana.edu/"]{Indiana University}}}
 @p{Office: @a[href:"https://www.soic.indiana.edu/about/maps.shtml"]{Lindley Hall}, Room 230C@~
    Email: @a[href:"mailto:samth@iu.edu" "samth@iu.edu"]@~
    Blog: @a[href:"http://scriptstoprograms.wordpress.com/" "Scripts to Programs"]@~
    Microblogging: @a[href: "http://twitter.com/samth/" "@samth"]@~
    Curriculum Vitae: @a[href: "cv.pdf"]{pdf}}
 @p{Papers: @a[href: "http://www.informatik.uni-trier.de/~ley/db/indices/a-tree/t/Tobin=Hochstadt:Sam.html"]{DBLP},
            @a[href: "http://scholar.google.com/citations?user=vMSSQbAAAAAJ"]{Google Scholar},
            @a[href: "http://arxiv.org/a/tobinhochstadt_s_1"]{arXiv},
            @a[href: "http://portal.acm.org/author_page.cfm?id=81319502825"]{ACM}}
 @p{Software: @a[href: "http://github.com/samth/"]{GitHub}}
}
 
@box['news "News"]{
@p{@b{I'm looking for new Ph.D
 students at 
@a[href: "http://cs.indiana.edu/"]{Indiana
 University Computer Science}, please @a[href: "mailto:samth@iu.edu"]{email me} if you are interested. }}


 @p{@b{New paper}: @a[href: "#ecoop15"]{
@i{Towards Practical Gradual Typing}} with @|asumu|, Earl Dean, Daniel Felty, @|MF|, @|robby|, @|mflatt|;
 to appear at @a[href: "http://conf.researchr.org/home/ecoop-2015"]{ECOOP 2015}}
                   
@p{@b{New paper}: @a[href:
                 "#manifesto"]{
@i{The Racket Manifesto}} with @|MF|, @|robby|, @|mflatt|, @|sk|, @|eli|, @|jay|;
 to appear at @a[href: "http://snapl.org/2015/index.html"]{SNAPL 2015}}

                   @p{@b{New paper}: @a[href:
                 "https://dl.dropboxusercontent.com/u/10275252/monotonic-references.pdf"]{
@i{Monotonic References for efficient gradual typing}} with Michael
M. Vitousek, Matteo Cimini, Jeremy Siek, and Ronald Garcia;
 to appear at @a[href: "http://conf.researchr.org/home/esop-2015"]{ESOP 2015}}

                   
@p{New draft: @a[href: "pycket-draft.pdf"]{@i{Pycket: a tracing
JIT  for a functional language}}, with Carl Friedrich Bolz,
Spenser Bauman, Jeremy Siek, Tobias Pape, Robert Hirschfeld, and
Vasily Krilichev.}

@p{New draft: @a[href: "parallel-typecheck-draft.pdf"]{
@i{Parallel Type-checking with Saturating LVars}},
       with Peter Fogg and Ryan Newton.}

@p{New draft: @a[href: "typed-clojure-draft.pdf"]{
@i{Practical Optional Typechecking for Clojure}},
       with Ambrose Bonnaire-Sargeant and Rowan Davies.}

@p{New draft: @a[href: "contract-monitoring-draft.pdf"]{
@i{Contract Monitoring Semantics as Patterns of Communication}},
       with Cameron Swords and Amr Sabry.}






@p{I am on the Program Committee for 
     @a[href: "http://conf.researchr.org/home/pldi2015"]{PLDI 2015}
     and the External Review Committee for POPL 2015.}

@p{I organized @a[href: "http://ifl2014.github.io/"]{IFL 2014} at
Northeastern University in Boston.}

@p{Our paper on @a[href: "#pycket-dyla"]{Pycket}, an experimental JIT
compiler for Racket, appeared at
@a[href: "http://www.lifl.fr/dyla14/"]{DYLA 2014}.}


@p{Our paper on @a[href: "#effectzoo"]{extending LVars with new effects} appeared 
 at @a[href: "http://conferences.inf.ed.ac.uk/pldi2014/"]{PLDI 2014}.}


@p{Our paper on the @a[href: "#network-calc"]{network calculus}, a
formalization of the ideas behind
@a[href: "http://tonyg.github.io/marketplace/"]{Marketplace}, 
appeared at @a[href: "http://flint.cs.yale.edu/esop2014/"]{ESOP 2014}}


}

@;{
Old news

@p{Our papers on @a[href: "#opt-coach"]{optimization coaching},
@a[href: "#fcc"]{gradual typing for first-class classes}, @a[href:
"#symexp"]{higher-order symbolic execution} and @a[href:
"#chaperones"]{chaperones} were presented at @a[href:
"http://splashcon.org/2012/"]{OOPSLA 2012}, and the paper on
@a[href: "#fcc"]{gradual typing for first-class classes} won best
student paper.}

@p{I was on the Program Committee for @a[href: "http://splashcon.org/2013/cfp/618"]{OOPSLA 2013}.}

@p{I presented a tutorial on Typed Racket at @a[href: "http://con.racket-lang.org/"]{RacketCon 2012}; both @a[href: "http://github.com/samth/tr-tutorial"]{code} and @a[href: "http://www.youtube.com/watch?v=w-fVHOxeEpM&feature=plcp"]{video} are available.}

@p{@a[href: "http://con.racket-lang.org/"]{RacketCon 2012} was held in Boston in October, and @a[href: "http://www.youtube.com/user/racketlang"]{videos} are now available.}

@p{@a[href: "http://wrigstad.com/stop12/"]{Scripts to Programs 2012} was a success, and the informal proceeding are now @a[href: "stop2012-proceedings.pdf"]{available}.}

@p{I was interviewed by @a[href: "http://carmine.blogs.com/"]{Charles Torre} from @a[href: "http://channel9.msdn.com/"]{Channel 9} about my work on @a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:modules"]{JavaScript modules}.  You can watch the video @a[href: "http://bit.ly/jsmodch9"]{here}.}

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
support the evolution of software.  I primarily work on
@a[href: "http://racket-lang.org"]{Racket} and
@a[href: "https://github.com/racket/typed-racket/"]{Typed Racket} as
well as with @a[href: "https://mozilla.org/research/"]{Mozilla
Research} on @a[href: "http://ecmascript.org"]{JavaScript}.}

@project['typed "Typed Racket"]{
@pdesc{I created and
        maintain @a[href: "https://github.com/racket/typed-racket/"]{Typed
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
@ul{
@li{@span{PLDI 2015}, Program Committee}
@li{@span{IFL 2014}, Chair}
@li{@span{POPL 2015}, External Review Committee}
@li{@span{DLS 2014}, Program Committee}
@li{@span{ICFP Student Research Competition 2014}, Program Committee}
@li{@a[href: "http://splashcon.org/2013/"]{OOPSLA 2013}, Program Committee}
@li{@a[href: "http://www.icfpconference.org/icfp2012/index.html"]{ICFP 2012}, Program Committee}
@li{@a[href: "http://wrigstad.com/stop/"]{STOP 2012}, Chair}
@li{@a[href: "http://scheme2011.ucombinator.org/"]{Scheme Workshop 2011}, Program Committee}
@li{@a[href: "http://nepls.org/Events/25"]{NEPLS 25}, Chair}
@li{@a[href: "http://www.mpi-sws.org/~dreyer/tldi2011/"]{TLDI 2011}, Program Committee}
@li{@a[href: #f]{FOOL 2010}, Program Committee}
@li{@a[href: #f]{TFP 2010}, Program Committee}
}}

@box['teaching "Teaching"]{ 

@ul{I'm teaching @a[href:
"http://www.cs.indiana.edu/classes/c211/"]{C211} in Fall 2014.}

@ul{I taught @a[href:
"http://homes.soic.indiana.edu/classes/spring2014/csci/p632-samth/"]{P632}
in Spring 2014.}

@ul{I taught @a[href:
"http://homes.soic.indiana.edu/classes/fall2013/csci/p532-samth/"]{P532}
in Fall 2013.}

@ul{
@li{ In Spring 2011, Spring 2012, and Spring 2013, I taught a new honors section of
@a[href: "http://www.ccs.neu.edu/course/cs2510h/"]{CS 2510} with
@a[href: "http://www.ccs.neu.edu/home/dvanhorn/"]{David Van Horn}.}

@li{ In Spring 2009, I taught @a[href: "211-09/"]{CS U211}.  }

@li{ In Fall 2005, I taught CS U213.}

@(papers edu-papers)

}}

@;@box['software "Software"]{}

@box['life "Personal"]{
@p{
  In the rest of my life, I play @a[href:"http://www.upa.org/"]{Ultimate} and I 
@a[href:"http://www.outdoors.org"]{go outside}.  }

@p{My wife, Katie Edmonds, is a post-doc in the 
@a[href:"http://www.indiana.edu/~dpglab/"]{Giedroc lab} in the IU Chemistry Department.}}



@; the end
}
}}
