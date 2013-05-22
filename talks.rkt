#lang at-exp racket

(provide (all-defined-out))
(require scribble/html "people.rkt")

(struct talk (title url loc date where))



(define analysis-talks
    (list
      (talk "Semantic Solutions to Program Analysis Problems"
            "fit11-talk.pdf"
            @a[href: "https://engineering.purdue.edu/~milind/pldi11fit/"]{Fun Ideas and Thoughts Session at the Conference on Programming Language Design and Implementation}
            "San Jose, CA" "June 2011")))

(define js-talks
    (list
      (talk "Research meets Application: Life on the EcmaScript Committee"
	    #f
	    "Northeastern University Ph.D. Seminar"
	    "Boston, MA" "2012")

      (talk "The Future of the Web: It's coming!"
             #f
            "Childrens Hospital developers group"
            "Boston, MA" "December 2011")))


(define macro-talks
   (list 

    (talk "Languages as Libraries"
	  #f
	  "Dagstuhl meeting on Foundations of Scripting Languages"
	  "Wadern, Germany" "January, 2012")


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

(define tr-talks
   (list
    (talk "From Principles to Practice with Class in the First Year"
          #f
           "OOPLSA PC Meeting Workshop"
           "Irvine, CA" "May 2013")

    (talk "Evolving Software From Scripts to Programs"
           #f
           "ETH Zurich Department of Computer Science"
           "Zurich, CH" "April, 2013")
    (talk "Evolving Software From Scripts to Programs"
           #f
           "Indiana University Department of Computer Science"
           "Bloomington, IN" "March, 2013")
    (talk "Evolving Software From Scripts to Programs"
           #f
           "Iowa State University Software Engineering Seminar"
           "Ames, IA" "March, 2013")
    (talk "Evolving Software From Scripts to Programs"
           #f
           "University of Idaho Department of Computer Science"
           "Moscow, ID" "March, 2013")
    
    (talk "Occurrence Typing"
	  #f
	  "Dagstuhl meeting on Foundations of Scripting Languages"
	  "Wadern, Germany" "January, 2012")


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

(define (talks ps)
  @div{@h2[class: 'subproject]{Talks} @(map format-talk ps)})

(define (format-talk t)
  @p[class: 'pub]{
    @(if (talk-url t) @a[href: (talk-url t) class: 'talktitle (talk-title t)] (talk-title t)),
    @(list (talk-loc t) ", " (talk-date t) ", " (talk-where t) ".")})
