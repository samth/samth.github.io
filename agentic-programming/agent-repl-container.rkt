#lang racket/base
(require "agent-repl-common.rkt" "agent-sandbox.rkt")

(define container (make-container))
(dynamic-wind
 void
 (lambda ()
   (printf "Sandbox: ~a (files in /work; removed at exit)\n" container)
   (run-repl
    "shell"
    (string-append
     "Run POSIX shell commands in /work in a disposable Python container. "
     "To run Python, use python -c 'code' or python - <<'PY' followed by code and PY. "
     "Create files and test them. Files persist for this conversation only. "
     "Python standard library only; no network, host files, or package downloads. "
     "10 seconds per command; 64 MiB workspace; 15-minute container lifetime. "
     "Print anything the user needs to retain before exiting.")
    (lambda (code) (run-container container code))))
 (lambda () (stop-container container)))
