#lang racket/base

(require racket/file racket/port racket/sandbox racket/system racket/random file/sha1)
(provide run-racket run-container make-container stop-container clean-text sandbox-image)

(define output-limit 16384)
(define sandbox-image
  "python@sha256:b3575dcf816cdacc5292df77a6e3e59b8941631078373a045efa2ac1e9c5c3b2")

(define (clean-text text)
  (regexp-replace* #px"[\u0000-\u0008\u000B-\u001F\u007F-\u009F]"
                   (substring text 0 (min (string-length text) output-limit)) ""))

;; Discard excess output as it arrives, rather than accumulating it first.
(define (capture)
  (define buffer (open-output-bytes))
  (define remaining output-limit)
  (define lock (make-semaphore 1))
  (values
   (make-output-port
    'bounded always-evt
    (lambda (bytes start end _non-block? _breakable?)
      (call-with-semaphore
       lock
       (lambda ()
         (define count (min remaining (- end start)))
         (write-bytes bytes buffer start (+ start count))
         (set! remaining (- remaining count))))
      (- end start))
    void)
   (lambda ()
     (string-append
      (clean-text (bytes->string/utf-8 (get-output-bytes buffer) #\?))
      (if (zero? remaining) "\n[output truncated]" "")))))

(define (run-racket code)
  (unless (<= (string-length code) 8192) (error 'sandbox "code exceeds 8192 characters"))
  (define-values (out result) (capture))
  (define evaluator #f)
  (dynamic-wind
   void
   (lambda ()
     (with-handlers ([(lambda (_) #t)
                      (lambda (e)
                        (display (if (exn? e) (exn-message e) "evaluation failed") out))])
       (parameterize ([sandbox-output out]
                      [sandbox-error-output out]
                      [sandbox-input #f]
                      [sandbox-memory-limit 64]
                      [sandbox-eval-limits '(2 64)]
                      [sandbox-path-permissions '()]
                      [sandbox-make-environment-variables make-environment-variables])
         (set! evaluator (make-evaluator 'racket/base))
         ;; Both evaluation and value printing happen under the sandbox's limits.
         (evaluator
          `(let ([input (open-input-string ,code)])
             (let loop ()
               (define form (read input))
               (unless (eof-object? form)
                 (call-with-values
                  (lambda () (eval form))
                  (lambda results
                    (for-each (lambda (v) (unless (void? v) (write v) (newline))) results)))
               (loop))))))))
   (lambda () (when evaluator (kill-evaluator evaluator))))
  (result))

;; The model controls only the final shell-command argument, never Docker flags.
(define (docker-command out seconds . args)
  (define docker (or (find-executable-path "docker") (error 'sandbox "install Docker")))
  (define custodian (make-custodian))
  (dynamic-wind
   void
   (lambda ()
     (parameterize ([current-custodian custodian]
                    [current-subprocess-custodian-mode 'kill]
                    [current-environment-variables (make-environment-variables #"PATH" #"/usr/bin:/bin")])
       (define-values (process stdout stdin stderr)
         (apply subprocess #f #f #f docker args))
       (close-output-port stdin)
       (define readers
         (for/list ([in (in-list (list stdout stderr))])
           (thread (lambda () (copy-port in out)))))
       (define finished? (sync/timeout seconds process))
       (unless finished? (subprocess-kill process #t))
       (subprocess-wait process)
       (for-each thread-wait readers)
       (if finished? (subprocess-status process) 'timeout)))
   (lambda () (custodian-shutdown-all custodian))))

(define (stop-container name)
  (docker-command (open-output-nowhere) 10 "rm" "-f" name))

(define (make-container)
  (define-values (out result) (capture))
  (define name (string-append "course-agent-" (bytes->hex-string (crypto-random-bytes 12))))
  (define status
    (docker-command
     out 15 "run" "--detach" "--rm" "--init" "--pull=never" "--name" name
     "--label=course-agent-sandbox=true" "--network=none" "--read-only"
     "--cap-drop=ALL" "--security-opt=no-new-privileges" "--pids-limit=32"
     "--memory=256m" "--memory-swap=256m" "--cpus=1" "--user=65534:65534"
     "--tmpfs" "/work:rw,nosuid,nodev,noexec,size=64m,mode=1777"
     "--tmpfs" "/tmp:rw,nosuid,nodev,noexec,size=16m,mode=1777"
     "--workdir=/work" "--env=HOME=/tmp" "--log-driver=none"
     sandbox-image "/bin/sleep" "900"))
  (unless (equal? status 0)
    (stop-container name)
    (error 'sandbox "container did not start: ~a" (result)))
  name)

(define (run-container name command)
  (unless (<= (string-length command) 8192) (error 'sandbox "command exceeds 8192 characters"))
  (define-values (out result) (capture))
  (define status
    (docker-command out 15 "exec" name
                    "/usr/bin/timeout" "-k" "1" "10" "/bin/sh" "-c" command))
  (when (member status '(timeout 124 137))
    ;; A timeout may leave descendants. End the whole sandbox, not just the client.
    (stop-container name)
    (display "\n[timeout: sandbox ended; restart the agent]" out))
  (string-append (format "Exit: ~a\n" status) (result)))
