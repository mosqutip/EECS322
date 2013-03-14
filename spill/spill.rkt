#lang plai

;; Global counter for naming unique variables
(define counter -1)

#|----- Helper Methods -----|#
;; ret-count : void -> void
(define (ret-count)
  (set! counter (add1 counter))
  counter)

;; dec-count : void -> void
(define (dec-count)
  (set! counter (sub1 counter))
  counter)

;; substitute : symbol -> symbol
(define (substitute prefix)
  (string->symbol (string-append
                   (symbol->string prefix)
                   (number->string (ret-count)))))

;; replace : L2i symbol symbol -> L2i
(define (replace sexp find-var repl-var)
  (cond
    [(equal? find-var sexp) repl-var]
    [(pair? sexp) (cons (replace (car sexp) find-var repl-var)
                        (replace (cdr sexp) find-var repl-var))]
    [else sexp]))

;; load-from-mem : symbol number -> string
(define (load-from-mem dst offset)
  (list dst '<- (list 'mem 'ebp offset)))

;; store-into-mem : symbol number -> string
(define (store-into-mem src offset)
  (list (list 'mem 'ebp offset) '<- src))
#|----- End helper methods -----|#

#|----- Main spill function -----|#
;; spill : L2i symbol number symbol -> (listof L2i)
(define (spill sexp var off pre)
  (match sexp
    [(or (list 'call _)
         (list 'tail-call _)
         (list 'cjump _ _ _ _ _)
         (list 'eax '<- (? list?))
         (list (? list?) '<- _))
     (let* ([new-var (substitute pre)]
            [new-sexp (replace sexp var new-var)])
       (if (equal? sexp new-sexp)
           (begin (dec-count) (list sexp))
           (list (load-from-mem new-var off) new-sexp)))]
    [(list a '<- (list 'mem b _))
     (let* ([new-var (substitute pre)]
            [new-sexp (replace sexp var new-var)])
       (cond
         [(equal? sexp new-sexp)
          (begin (dec-count) (list sexp))]
         [(and (equal? a var)
               (equal? b var))
          (list (load-from-mem new-var off) new-sexp (store-into-mem new-var off))]
         [(equal? a var)
          (list new-sexp (store-into-mem new-var off))]
         [else
          (list (load-from-mem new-var off) new-sexp)]))]
    [(list a '<- b)
     (cond
       [(and (equal? a b)
             (equal? a var))
        (list #\nul)]
       [(equal? b var)
        (list (load-from-mem a off))]
       [(equal? a var)
        (list (store-into-mem b off))]
       [else (list sexp)])]
    [(list a '<- b op c)
     (let* ([new-var (substitute pre)]
            [new-sexp (replace sexp var new-var)])
       (cond
         [(and (equal? a var)
               (or (equal? b var)
                   (equal? c var)))
          (list (load-from-mem new-var off) new-sexp (store-into-mem new-var off))]
         [(equal? a var)
          (list new-sexp (store-into-mem new-var off))]
         [(or (equal? b var)
              (equal? c var))
          (if (equal? sexp new-sexp)
              (begin (dec-count) sexp)
              (list (load-from-mem new-var off) new-sexp))]
         [else (begin (dec-count) (list sexp))]))]
    [(list a op b)
     (let* ([new-var (substitute pre)]
            [new-sexp (replace sexp var new-var)])
       (cond
         [(equal? a var)
          (list (load-from-mem new-var off) new-sexp (store-into-mem new-var off))]
         [(equal? b var)
          (list (load-from-mem new-var off) new-sexp)]
         [else (begin (dec-count) (list sexp))]))]
    [else (list sexp)]))
#|----- End main spill function -----|#

#|----- File IO functions -----|#
; define a list of input strings over which to iterate the spill function
(define input
  (file->list "L2s.input"))

;; Create a temporary output string that holds the concatenation of all instructions
(define output-string (open-output-string))

;; Grab each instruction and add it to our string
(map (λ (line)
       (let ([output (spill line (second input) (third input) (fourth input))])
         (map (λ (inst)
                (if (not (equal? inst #\nul))
                    (displayln inst output-string)
                    (displayln "")))
              output)))
     (first input))

;; Output the final instruction string to a file, in list form
(with-output-to-file "L2s.output" #:exists 'replace
  (λ () (display (list (get-output-string output-string)))))
#|----- End file IO functions -----|#