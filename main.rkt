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

   @meta[http-equiv: "Content-Type" content: "text/html" charset: "UTF-8"]
   @css{http://fonts.googleapis.com/css?family=PT+Sans}
   @css{http://fonts.googleapis.com/css?family=Paprika}
   @css{http://fonts.googleapis.com/css?family=Nobile}
   @css{modern_academic_css.css}
   }

@body{



@div[id: 'contents]{

             @; @p{Programming language semanticists should be the obstetricians of programming languages, not their coroners.
@; @|~| @div[id: "nameright"]{- John C. Reynolds}}}}}


@box['name sth]{
@div[class: "right"]{
   @p{@img[id: "photo" src: "tree.jpg" alt: "Tree" title:"Winter"]}
   @div{@p[style: "font-size: 85%;"]{@i{The most important decisions a scholar makes are what problems to work on.}  - @a[href: "http://www.tobinproject.org/about/james-tobin"]{James Tobin}}}}
 @div{

    @p{Associate Professor @~
    @a[href: "http://racket-lang.org/people.html"]{PLT} &
     @a[href: "http://wonks.github.io"]{PL} @"@"
    @a[href: "http://cs.indiana.edu/"]{Department of Computer Science}@~
    @a[href: "http://www.indiana.edu/"]{Indiana University}}}
 @p{Office: @a[href:"https://cs.indiana.edu/about/facilities.html"]{Luddy Hall}, Room 3022@~
    Email: @a[href:"mailto:samth@iu.edu" "samth@iu.edu"]@~
   Microblogging: @a[href: "http://twitter.com/samth/" "@samth"], @a[href: "https://bsky.app/profile/samth.bsky.social" "@samth.bsky.social"]@~
    Curriculum Vitae: @a[href: "cv.pdf"]{pdf}}
 @p{Papers: @a[href: "https://dblp.uni-trier.de/pid/56/3287.html"]{DBLP},
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

@p{@b{New paper}: @a[href: "#gc-serialized"]{
@i{Garbage Collection for Mostly Serialized Heaps}} with @|chaitanya| and @|rrnewton|;
appeared at @a[href: "https://ismm24.sigplan.org/"]{ISMM 2024}}

@p{@b{New paper}: @a[href: "#rhombus"]{
@i{Rhombus: A New Spin on Macros without All the Parentheses}} with @|mflatt| and others;
appeared at @a[href: "https://2023.splashcon.org/track/splash-2023-oopsla"]{OOPSLA 2023}}

@p{@b{New papers}: @a[href: "#sham"]{
@i{Sham: A DSL for Fast DSLs}} with @|rajan-walia| and @|chung-chieh-shan| and @a[href: "#type-checking-extracted"]{
@i{Type Checking Extracted Methods}} with @|yuquan-fu|;
both appeared in @a[href: "https://programming-journal.org/"]{Art, Science, and Engineering of Programming} 2022}

@p{@b{New paper}: @a[href: "#forward-builds"]{
@i{Forward build systems, formally}} with @|spall| and @|neil-mitchell|;
appeared at @a[href: "https://popl22.sigplan.org/home/CPP-2022"]{CPP 2022}}

@p{@b{New paper}: @a[href: "#corpse-reviver"]{
@i{Corpse reviver: sound and efficient gradual typing via contract verification}} with @|cameron-moy|, @|phuc|, and @|dvh|;
appeared at @a[href: "https://popl21.sigplan.org/"]{POPL 2021}}

@p{Our recent work includes advances in gradual typing, domain-specific languages,
 JIT compilers,  and program verifiers, among other areas of
  PL design and implementation.}

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

@project['metaprogramming "Domain-Specific Languages"]{
      @pdesc{I develop techniques and tools for creating efficient
      domain-specific languages, particularly for high-performance
      computing and probabilistic programming. Additionally, developing @racket, I have helped to build a programmable
      programming language that allows developers to create
      custom languages for everything from pattern matching
      to type checking.}
       @(papers dsl-papers)}

@project['analysis "Analysis and Verification"]{
      @pdesc{I am developing  analysis and verification
      techniques for modular programs with rich specifications.}
       @(papers analysis-papers)
       @(talks analysis-talks)}

@project['systems "Systems and Performance"]{
      @pdesc{I work on garbage collection, memory management,
      and performance optimization for functional languages
      and parallel systems. I also work on formal 
      foundations and practical implementations of build systems, 
      focusing on correct dependency tracking and efficient incremental builds.}
       @(papers systems-papers)}


@project['industry "Industry Collaboration"]{
 @pdesc{I have collaborated with industry partners on programming language design and implementation. 
      In collaboration with @a[href:"https://mozillalabs.com/"]{Mozilla Research} and ECMA Technical Committee 39, I
      worked on the next version of the JavaScript language,
      focusing on making JavaScript an effective language for building
      large-scale web applications. I also worked with
      @a[href: "http://labs.oracle.com/projects/plrg/"]{Sun Labs
      Programming Language Research Group} to
      develop @a[href: "http://projectfortress.java.net/"]{Fortress}, a
      new language for high-performance, multicore and scientific
      computing.}
  @(papers industry-papers)
  @div{@h2[class: 'subproject]{JavaScript Proposals}
  @p{@a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:modules"]{Modules} and
      @a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:module_loaders"]{Module Loaders}. 
      With @|dherman|.
     @~ Drafts from September 2011.}
  @p{@a[href: "http://wiki.ecmascript.org/doku.php?id=harmony:private_name_objects"]{Private Names}. 
      With @dherman and Allen Wirfs-Brock.
     @~ Draft from September 2011.}
  }
 @(talks js-talks)}
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

@p{I regularly teach graduate and undergraduate courses in programming languages, especially @a[href: "http://www.cs.indiana.edu/classes/c211/"]{C211 (Introduction to Computer Science)}.}

@(papers edu-papers)

}

@;@box['software "Software"]{}

@box['life "Personal"]{
@p{
  In the rest of my life, I play @a[href:"https://bloomingtonultimate.org/"]{Ultimate} and I 
@a[href:"https://sycamorelandtrust.org/"]{go outside}.  }

@p{My wife, Katie Edmonds, is a Scientist in the 
@a[href:"http://www.chem.indiana.edu/"]{IU Chemistry} Department.}}



@; the end
}}
}}
