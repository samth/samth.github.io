#lang scribble/html

@(require racket/list racket/match "utils.rkt"
	  "people.rkt" "papers.rkt" "talks.rkt")

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

@box['name sth]{
@div[class: "right"]{
      @p{@img[id: "photo" src: "tree.jpg" alt: "Tree" title:"Winter"]}
      @div{@p{The most important decisions a scholar makes are what problems to work on. @|~| @div[id: "nameright"]{- James Tobin}}}}
 @div{

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
}
 
@box['news "News"]{
@p{I presented a tutorial on Typed Racket at RacketCon 2012; both @a{code} and @a{video} are available.}		   
@p{Our papers on optimization coaching, gradual typing for first-class classes, higher-order symbolic execution and chaperones were presented at @a[href: "http://splashcon.org/2012/"]{OOPSLA 2012}.}
@p{@a[href: "http://con.racket-lang.org/"]{RacketCon 2012} was held in Boston in October, and @a[href: "http://www.youtube.com/user/racketlang"]{videos} are now available.}
@p{@a[href: "http://wrigstad.com/stop12/"]{Scripts to Programs 2012} was a success, and the informal proceeding are now @a[href: "stop2012-proceedings.pdf"]{available}.}
@p{I was interviewed by @a[href: "http://carmine.blogs.com/"]{Charles Torre} from @a[href: "http://channel9.msdn.com/"]{Channel 9} about my work on @a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:modules"]{JavaScript modules}.  You can watch the video @a[href: "http://bit.ly/jsmodch9"]{here}.}}

@;{
Old news

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
@ul{
@li{@span{IFL 2014}, Chair}
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
@ul{
@li{ In Spring 2011 and Spring 2012, I taught a new honors section of
@a[href: "http://www.ccs.neu.edu/course/cs2510h/"]{CS 2510} with
@a[href: "http://www.ccs.neu.edu/home/dvanhorn/"]{David Van Horn}.}

@li{ In Spring 2009, I taught @a[href: "211-09/"]{CS U211}.  }

@li{ In Fall 2005, I taught CS U213.}
}}

@;@box['software "Software"]{}

@box['life "Personal"]{
@p{
  In the rest of my life, I play @a[href:"http://www.upa.org/"]{Ultimate} and I 
@a[href:"http://www.outdoors.org"]{go outside}.  }

@p{My wife, Katie Edmonds, is a post-doc in the 
@a[href:"http://www.bumc.bu.edu/phys-biophys/people/faculty/marintchev/"]{Marinchev lab} at the Boston University Medical Campus.}}



@; the end
}
}}