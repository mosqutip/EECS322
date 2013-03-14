#lang plai
(require racket/mpair)

; program input
(define input (first (file->list "L2.input")))

; output string
(define output-string (open-output-string))
(define temp-output-string (open-output-string))

;; compile: L2i -> L1i
(define (compile L2i)
  (for ([i (in-range (length input))])
    (let ([inst (list-ref input i)])
      (with-output-to-file "L2l.input" #:exists 'replace
        (λ () (displayln inst)))
      
      ;; offset for spill variables
      (define offset -8)
      
      ; prefix for spill variables
      (define prefix 's_)
      
      ; counter for spill variables
      (define counter -1)
      
      ; num args
      (define numargs 0)
      
      ; spill frame
      (define (make-spill-frame loc)
        (if (= loc 0)
            `((esp -= ,numargs)
              ((mem ebp -4) <- edi)
              ((mem ebp -8) <- esi))
            `((edi <- (mem ebp -4))
              (esi <- (mem ebp -8))
              (esp += ,numargs))))
      
      ;; replace : L2i symbol symbol -> L2i
      (define (replace sexp find-var repl-var)
        (cond
          [(equal? find-var sexp) repl-var]
          [(pair? sexp) (cons (replace (car sexp) find-var repl-var)
                              (replace (cdr sexp) find-var repl-var))]
          [else sexp]))
      
      ;; ret-count : void -> number
      (define (make-count)
        (set! counter (add1 counter))
        counter)
      
      ;; make-offset : void -> number
      (define (make-offset)
        (set! offset (- offset 4))
        offset)
      
      ;; make-sym : symbol -> symbol
      (define (make-sym pre)
        (string->symbol (string-append
                         (symbol->string pre)
                         (number->string (make-count)))))
      
      ; run liveness and graph to test a coloring
      (system "/Applications/racket/bin/racket graph.rkt")
      
      ; store the result of a graph color try
      (define result
        (second (file->list "L2g.output")))

      ; get the variables in a coloring attempt
      (define vars
        (file->list "vars.output"))
      
      ; compose-func
      (define (compose-func sexp)
        (let ([new-sexp (take sexp (- (length sexp) 1))]
              [last-element (list-ref sexp (- (length sexp) 1))])
          (if (equal? last-element '(return))
              `(,(first new-sexp)
                ,@(make-spill-frame 0)
                ,@(rest new-sexp)
                ,@(make-spill-frame 1)
                ,last-element)
              `(,(first new-sexp)
                ,@(make-spill-frame 0)
                ,@(rest new-sexp)
                ,last-element
                ,@(make-spill-frame 1)))))
      
      ;; setup-spill-file : symbol, number, symbol -> void
      (define (setup-spill-file var off sym)
        (with-output-to-file "L2s.input" #:exists 'replace
          (λ () 
            (begin (pretty-display (first (file->list "L2l.input")))
                   (display var)
                   (display " ")
                   (display off)
                   (display " ")
                   (display sym)))))
      
      ;; replace-vars : L2i, listof symbol -> void
      (define (replace-vars prog color-list)
        (foldl (λ (pair res)
                 (let* ([var (first pair)]
                        [color (second pair)])
                   (replace res var color)))
               prog
               color-list))
      
      ;; remove-redundancies : L2i -> L2i
      (define (remove-redundancies prog)
        (map (λ (inst)
               (match inst
                 [(list a '<- b)
                  (if (and
                       (symbol? a)
                       (symbol? b)
                       (equal? a b))
                      (remove inst prog)
                      (displayln inst temp-output-string))]
                 [else (displayln inst temp-output-string)]))
             prog))
      
      ;; spill-loop : number -> void
      (define (spill-loop iter)
        (case result
          [(#f)
           (begin
             (set! numargs (+ numargs 4))
             (setup-spill-file (list-ref vars iter) (make-offset) (make-sym prefix))
             (system "/Applications/racket/bin/racket spill.rkt")
             (system "/Applications/racket/bin/racket graph.rkt")
             (pretty-display (file->list "L2g.output"))
             (set! result (second (file->list "L2g.output")))
             (spill-loop (add1 iter)))]
          [else
           (begin (if (> numargs 0)
                      (remove-redundancies
                       (replace-vars (compose-func (first (file->list "L2l.input"))) result))
                      (remove-redundancies
                       (replace-vars (first (file->list "L2l.input")) result)))
                  (pretty-display
                   (list (get-output-bytes temp-output-string #t 0
                                           (- (string-length (get-output-string temp-output-string)) 1)))
                   output-string))]))
      
      ; start spilling the function
      (spill-loop 0)))
  
  (with-output-to-file "L2.output" #:exists 'replace
    (λ ()
      (display (list (get-output-string output-string))))))

; run the main compile function
(compile input)