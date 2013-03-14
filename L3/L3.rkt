#lang plai

; counter for variables
(define var-counter -1)

; counter for labels
(define lab-counter -1)

; prefix for variables
(define var-prefix 'u_)

; prefix for labels
(define lab-prefix ':lab)

; rename duplicate variables
(define dup-set (set))

; set of reserved words
(define reserved-set (set 'mem 'goto 'cjump 'call 'tail-call
                          'return 'allocate 'array-error))

; variable for duplicates
(define dup-var 'change)

; variable for bodies with multiple variables of the same name
(define new-body '())

;; ret-count : num -> number
(define (make-count num)
  (if (equal? num 0)
      (begin (set! var-counter (add1 var-counter))
             var-counter)
      (begin (set! lab-counter (add1 lab-counter))
             lab-counter)))

;; make-sym : num -> symbol
(define (unique-symbol num)
  (if (equal? num 0)
      (string->symbol (string-append
                       (symbol->string var-prefix)
                       (number->string (make-count num))))
      (string->symbol (string-append
                       (symbol->string lab-prefix)
                       (number->string (make-count num))))))

; prefix for main function
(define main-prefix
  (string->symbol (string-append ":main_func_prefix_"
                                 (number->string (random 1000)))))

;; label? : symbol/number -> boolean
(define (label? a)
  (if (symbol? a)
      (equal? #\: (string-ref (symbol->string a) 0))
      #f))

;; encode : symbol/number -> symbol/number
(define (encode v)
  (if (number? v)
      (+ (* v 2) 1)
      v))

; set of biops
(define biop-set (set '+ '- '* '< '<= '=))

; set of predicates
(define pred-set (set 'a? 'number?))

; list of argument registers
(define arg-list (list 'eax 'ecx 'edx))

;; biop? : symbol -> boolean
(define (biop? a)
  (not (set-empty? (set-intersect biop-set (set a)))))

;; pred? : symbol -> boolean
(define (pred? a)
  (not (set-empty? (set-intersect pred-set (set a)))))

;; make-mem-assigns : symbol, number, listof symbol -> listof L2i
(define (make-mem-assigns symbol len args)
  (let ([temp-list '()])
    (for ([i (in-range len)])
      (set! temp-list (append temp-list `(((mem ,symbol ,(+ (* i 4) 4))
                                           <- ,(encode (list-ref args i)))))))
    temp-list))

;; make-fae-assigns : listof v -> listof d
(define (make-fae-assigns args)
  (let* ([temp-list '()]
         [len (length args)])
    (for ([i (in-range len)])
      (set! temp-list (append temp-list `((,(list-ref args i) <- ,(encode (list-ref arg-list i)))))))
    temp-list))

;; assign-regs : listof v -> listof d
(define (assign-regs args)
  (let* ([temp-list '()]
         [len (length args)])
    (for ([i (in-range len)])
      (set! temp-list (append temp-list `((,(list-ref arg-list i) <- ,(encode (list-ref args i)))))))
    temp-list))

;; make-return-call : L2i -> L2i
(define (make-return-call sexp flag)
  (if (equal? 1 flag)
      (append sexp (list '(return)))
      sexp))

;; replace-var : L3i, symbol, symbol -> void
(define (replace-var sexp find-var repl-var)
  (cond
    [(equal? find-var sexp) repl-var]
    [(pair? sexp) (cons (replace-var (car sexp) find-var repl-var)
                        (replace-var (cdr sexp) find-var repl-var))]
    [else sexp]))

;; compile : listof L3i -> listof L2i
(define (compile sexp)
  (match sexp
    [(list 'let (list (list var expr)) body)
     (compile-let var expr body)]
    [(list 'if v e1 e2)
     (compile-if v e1 e2)]
    [else
     (compile-d sexp 'eax 1)]))

;; compile-let : listof L3i -> listof L2i
(define (compile-let var expr body)
  (if (set-member? (set-union dup-set reserved-set) var)
      (begin (set! dup-var (unique-symbol 0))
             (set! new-body (replace-var body var dup-var))
             (set! dup-set (set-union dup-set (set dup-var))))
      (begin (set! dup-var var)
             (set! new-body body)))
  (set! dup-set (set-union dup-set (set var)))
  (match expr
    [(or (? number? expr)
         (? symbol? expr)
         (? label? expr))
     (append (list (list dup-var '<- (encode expr))) (compile new-body))]
    [else
     (append (compile-d expr dup-var 0) (compile new-body))]))

;; compile-if : L3i -> listof L2i
(define (compile-if v e1 e2)
  (let* ([t (unique-symbol 1)]
         [f (unique-symbol 1)])
    `((cjump ,(encode v) = 1 ,f ,t)
      ,t
      ,@(compile e1)
      ,f
      ,@(compile e2))))

;; compile-d : listof L3i -> listof L2i
(define (compile-d sexp symbol flag)
  (match sexp
    [(list (? biop? a) v1 v2)
     (make-return-call (compile-biop a (encode v1) (encode v2) symbol) flag)]
    [(list (? pred? a) v)
     (make-return-call (compile-pred a (encode v) symbol) flag)]
    [(list 'new-array v1 v2)
     (make-return-call `((eax <- (allocate ,(encode v1) ,(encode v2)))
                         (,symbol <- eax)) flag)]
    [(list 'new-tuple args ...)
     (make-return-call
      (let ([len (length args)])
        (append `((eax <- (allocate ,(encode len) 1))
                  (,symbol <- eax))
                (make-mem-assigns symbol len args))) flag)]
    [(list v (list args ...) body)
     (if (> (length args) 0)
         (append (list v)
                 (make-fae-assigns args)
                 (compile body))
         (append (list v)
                 (compile body)))]
    [(list 'aref v1 v2)
     (make-return-call
      (let* ([tmp (unique-symbol 0)]
             [t1 (unique-symbol 1)]
             [t2 (unique-symbol 1)]
             [f (unique-symbol 1)])
        `((,symbol <- ,(encode v2))
          (,symbol >>= 1)
          (,tmp <- (mem ,v1 0))
          (cjump ,symbol < 0 ,f ,t1)
          ,t1
          (cjump ,symbol < ,tmp ,t2 ,f)
          ,f
          (eax <- (array-error ,v1 ,(encode v2)))
          (return)
          ,t2
          (,symbol *= 4)
          (,symbol += ,v1)
          (,symbol <- (mem ,symbol 4)))) flag)]
    [(list 'aset v1 v2 v3)
     (make-return-call
      (let* ([tmp (unique-symbol 0)]
             [t1 (unique-symbol 1)]
             [t2 (unique-symbol 1)]
             [f (unique-symbol 1)])
        `((,symbol <- ,(encode v2))
          (,symbol >>= 1)
          (,tmp <- (mem ,v1 0))
          (cjump ,symbol < 0 ,f ,t1)
          ,t1
          (cjump ,symbol < ,tmp ,t2 ,f)
          ,f
          (eax <- (array-error ,v1 ,(encode v2)))
          (return)
          ,t2
          (,symbol *= 4)
          (,symbol += ,v1)
          ((mem ,symbol 4) <- ,(encode v3))
          (,symbol <- 1))) flag)]
    [(list 'alen v)
     (make-return-call
      `((,symbol <- (mem ,v 0))
        (,symbol <<= 1)
        (,symbol += 1)) flag)]
    [(list 'print v)
     (make-return-call
      `((eax <- (print ,(encode v)))
        (,symbol <- eax)) flag)]
    [(list 'make-closure l v)
     (make-return-call
      `((eax <- (allocate 5 0))
        (,symbol <- eax)
        ((mem ,symbol 4) <- ,l)
        ((mem ,symbol 8) <- ,(encode v))) flag)]
    [(list 'closure-proc v)
     (let* ([tmp (unique-symbol 0)]
            [t (unique-symbol 1)]
            [f (unique-symbol 1)])
       (make-return-call
        `((,symbol <- 1)
          (,symbol >>= 1)
          (,tmp <- (mem ,v 0))
          (cjump ,symbol < ,tmp ,t ,f)
          ,f
          (eax <- (array-error ,v 1))
          (return)
          ,t
          (,symbol *= 4)
          (,symbol += ,v)
          (,symbol <- (mem ,symbol 4))) flag))]
    [(list 'closure-vars v)
     (let* ([tmp (unique-symbol 0)]
            [t (unique-symbol 1)]
            [f (unique-symbol 1)])
       (make-return-call
        `((,symbol <- 3)
          (,symbol >>= 1)
          (,tmp <- (mem ,v 0))
          (cjump ,symbol < ,tmp ,t ,f)
          ,f
          (eax <- (array-error ,v 3))
          (return)
          ,t
          (,symbol *= 4)
          (,symbol += ,v)
          (,symbol <- (mem ,symbol 4))) flag))]
    [(list f args ...)
     (if (equal? 1 flag)
         (append (assign-regs args)
                 `((tail-call ,f)))
         (append (assign-regs args)
                 `((call ,f))
                 `((,symbol <- eax))))]
    [else (make-return-call `((eax <- ,(encode sexp))) flag)]))

;; compile-biop : symbol, v, v, symbol -> L2i
(define (compile-biop op v1 v2 symbol)
  (match op
    ['+
     (append
      (list `(,symbol <- ,v1))
      (list `(,symbol += ,v2))
      (list `(,symbol -= 1))
      (list `(eax <- ,symbol)))]
    ['-
     (append
      (list `(,symbol <- ,v1))
      (list `(,symbol -= ,v2))
      (list `(,symbol += 1))
      (list `(eax <- ,symbol)))]
    ['*
     (append
      (list `(,symbol <- ,v1))
      (list `(,symbol *= ,v2))
      (list `(,symbol -= ,v1))
      (list `(,symbol -= ,v2))
      (list `(,symbol += 3))
      (list `(,symbol >>= 1))
      (list `(eax <- ,symbol)))]
    [else
     (append (list `(,symbol <- ,v1 ,op ,v2))
             (list `(,symbol += ,symbol))
             (list `(,symbol += 1)))]))

;; compile-pred : symbol, v, symbol -> L2i
(define (compile-pred pred v symbol)
  (match pred
    ['a?
     (append
      (list `(,symbol <- ,v))
      (list `(,symbol &= 1))
      (list `(,symbol *= -2))
      (list `(,symbol += 3)))]
    ['number?
     (append
      (list `(,symbol <- ,v))
      (list `(,symbol &= 1))
      (list `(,symbol <<= 1))
      (list `(,symbol += 1)))]))

#|----- File IO functions -----|#
(define input
  (file->list "L3.input"))

(define compiled-expr
  (map (λ (line)
         (let ([output (compile line)])
           (begin (set! dup-set (set))
                  output)))
       (first input)))

(define output-list
  (cons `((call ,main-prefix))
        (cons (cons main-prefix (car compiled-expr))
              (cdr compiled-expr))))

(with-output-to-file "L3.output" #:exists 'replace
  (λ () (pretty-display output-list)))
#|----- End file IO functions -----|#