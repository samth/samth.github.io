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
  
  ;; title : String
  ;; fname : String
  ;; content : (list Xexpr)
  (define-struct sect (title fname lnk content))
  
  (define the-table (make-hash-table))
  
  (define (page key title link-title . content)
    (let ([fname (string-append (symbol->string key) ".html")])
      (hash-table-put! the-table key
                       (make-sect title fname link-title content))))
  
  (define (links current-key)
    (hash-table-map the-table
                    (lambda (k v)
                      (if (eq? current-key k)
                          "" #;`(td nbsp) #;`(td (h1 ,(sect-title v)))
                          `(td (h2 ,(link (sect-lnk v) (sect-fname v))))))))
  
  (define (complete-page sect cur-key)
    (define table-size (number->string (+ 2 (hash-table-count the-table))))
    (define title (sect-title sect))
    `(html (head (title ,title))
           (body (table (tr (td (h1 ,title)) (td 'nbsp 'nbsp) ,@(links cur-key))
                        (tr (td ((colspan ,table-size)) ,@(sect-content sect)))))))

  (define (write-xexpr e fname) (with-output-to-file fname 
                                  (lambda () (display-xml/content (xexpr->xml e))) 'replace))

  
  (define (render-sect k sect)
    (write-xexpr (complete-page sect k) (sect-fname sect)))
  
  (define (go)
    (hash-table-for-each  the-table render-sect))
  
  (define papers (list 
                  (paper "Sam Tobin-Hochstadt and Matthias Felleisen" 
                         "Interlanguage Migration: From Scripts to Programs" "tmp/dls.pdf"
                         "To appear in Dynamic Languages Symposium, October 2006")
                  (paper "Sam Tobin-Hochstadt and Eric Allen"
                         "A Core Calculus of Metaclasses" "http://research.sun.com/projects/plrg/fool2005.pdf"
                         "In Foundations of Object Oriented Languages, January 2005")
                  (paper "Eric Allen, David Chase, Joe Hallett, Victor Luchangco, Jan-Willem Maessen, Sukyoung Ryu, Guy Steele and Sam Tobin-Hochstadt."
                         "The Fortress Language Specification" "http://research.sun.com/projects/plrg/fortress.pdf"
                         "Sun Microsystems Technical Report, Version 1.0 α")))

  (define pubs (page 'pubs "Publications" "Publications"
                     `(ul ,@papers)))
  
  (define soft (page 'soft "Software" "Software"
                     `(ul (li (b "Pattern Matching:") "I am the maintainer of the" ,(link/mzlib "match.ss" ) "and" 
                              ,(link/mzlib "plt-match.ss") 
                              "libraries in PLT Scheme, which provide a convenient syntax for pattern matching on values."))))
  
  (define body 
    (page 'index "Sam Tobin-Hochstadt" "Home"
          `(p "I'm a graduate student in the " ,(link "PLT ""http://www.ccs.neu.edu/scheme") "research group,"
              "working with" ,(link "Matthias Felleisen" "http://www.ccs.neu.edu/home/matthias")
              "at" ,(link  "Northeastern University" "http://www.ccs.neu.edu") ".")
          `(p "I work on the integration of typed"
             "and untyped programming languages, and on novel type systems for Scheme.")          
          ))
  
  (define contact (page 'contact "Contact" "Contact"
                        `(p (b "Office:") "Room 308, West Village H.")
                        `(p (b "Email:") ,(link `(code "samth@ccs.neu.edu") "mailto:samth@ccs.neu.edu"))
                        `(p (b "Phone:") (code "617 373 7920"))))
  
  (define teaching (page 'teaching "Teaching" "Teaching"
                         "In the Fall of 2005, I taught" (link "CSU 213" "213") "."))
  
  
  #;(define (go) 
    (write-xexpr pubs "pubs.html")
    (write-xexpr soft "software.html")
    (write-xexpr contact "contact.html")
    (write-xexpr teaching "teaching.html")
    (write-xexpr body "index.html"))
  
  (go)
  
  )