(module index mzscheme
  
  (require (lib "xml.ss" "xml"))
  
  (define (paper authors title url note)
    `(li ,authors (br) ,(link title url) (br) ,note))
  
  (define (section name . rest)
    `(p (h2 ,name) ,@rest))
  
  (define (link txt tgt)
    `(a ((href ,tgt)) ,txt))
  
  (define (link/svn txt path)
    (link txt (string-append "http://svn.plt-scheme.org/plt/trunk/" path)))
  
  (define (link/mzlib fname)
    (link/svn `(code ,fname) (string-append "collects/mzlib/" fname)))
  
  (define body `(html 
                 (head (title "Sam Tobin-Hochstadt"))
                 (body
                  (h1 "Sam Tobin-Hochstadt")
                  (p "I'm a fourth year student in the " ,(link "PLT ""http://www.ccs.neu.edu/scheme") "research group"
                     "at" ,(link  "Northeastern University" "http://www.ccs.neu.edu") ".")
                  (p "I work on the integration of typed"
                     "and untyped programming languages, and on novel type systems for Scheme.")
                  ,(section "Publications"
                     `(ul 
                      ,(paper "Sam Tobin-Hochstadt and Matthias Felleisen" 
                             "Interlanguage Migration: From Scripts to Programs" "tmp/dls.pdf"
                             "To appear in Dynamic Languages Symposium, October 2006")
                      ,(paper "Sam Tobin-Hochstadt and Eric Allen"
                             "A Core Calculus of Metaclasses" "http://research.sun.com/projects/plrg/fool2005.pdf"
                             "In Foundations of Object Oriented Languages, January 2005")
                      ,(paper "Eric Allen, David Chase, Joe Hallett, Victor Luchangco, Jan-Willem Maessen, Sukyoung Ryu, Guy Steele and Sam Tobin-Hochstadt."
                             "The Fortress Language Specification" "http://research.sun.com/projects/plrg/fortress.pdf"
                             "Sun Microsystems Technical Report, Version 1.0 α")
                      ))
                  ,(section "Software"
                            `(ul (li (b "Pattern Matching:") "I am the maintainer of the" ,(link/mzlib "match.ss" ) "and" 
                                     ,(link/mzlib "plt-match.ss") 
                                     "libraries in PLT Scheme, which provide a convenient syntax for pattern matching on values.")))
                  ,(section "Teaching"
                            "In the Fall of 2005, I taught" (link "CSU 213" "213") ".")
                  ,(section "About Me"
                            `(p (b "Office:") "Room 308, West Village H.")
                            `(p (b "Email:") ,(link `(code "samth@ccs.neu.edu") "mailto:samth@ccs.neu.edu") ".")
                            `(p (b "Phone:") (code "617 373 7920"))))))
  
  (define page body)
  
  (define (write-xexpr e fname) (with-output-to-file fname 
                                  (lambda () (display-xml/content (xexpr->xml e))) 'replace))
  
  (define (go) (write-xexpr page "index.html"))
  
  (go)
  
  )