#lang racket/base
(require "agent-repl-common.rkt" "agent-sandbox.rkt")

(run-repl
 "racket"
 (string-append
  "Evaluate Racket expressions, without #lang, in a fresh racket/base sandbox. "
  "Include all definitions in each call. Data must come from the conversation. "
  "No user files, network, subprocesses, or inherited environment. "
  "Each call has 2 seconds, 64 MiB memory, and bounded output.")
 run-racket)
