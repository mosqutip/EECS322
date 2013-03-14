#lang plai

(define counter -1)
(define func-list '())

(define (compile-L5e a-l5e bound-ids)
  (type-case L5E a-l5e
    (lambda-e (args body)
              (let* ([sym (make-sym)]
                     [lab (make-lab sym)]
                     [vars (free-ids-sub body (append args bound-ids))])
                (begin
                  (add-func lab args vars body)
                  `(make-closure ,lab (new-tuple ,vars)))))
    (let-e (bind e2)
           (let* ([x (first bind)]
                  [e1 (second bind)])
             (if (equal? 'lambda (first e1))
                 (let ([new-lab (make-lab x)])
                   `(let ([,x (make-closure ,new-lab ,('new-tuple (free-ids-sub e2 (second e1))))])
                      ,(replace (compile-L5e e2 (append (second e1) bound-ids)) x new-lab)))
                 a-l5e)))
    (letrec-e (bind e2)
              (let* ([x (first bind)]
                     [e1 (second bind)])
                (compile-L5e `(let ([,x (new-tuple 0)])
                                (begin-e (aset ,x 0 ,(replace e1 x ('aref x 0)))
                                         ,(replace e2 x ('aref x 0)))) (cons x bound-ids))))
    (begin-e (e1 e2)
             (list (compile-L5e e1 bound-ids)
                   (compile-L5e e2 bound-ids)))
    (app-e (func args)
           (cond
             [(= (length args) 1)
              (let ([name (make-sym)])
                `(let ([,name ,(compile-L5e func bound-ids)])
                   ((closure-proc ,name) (closure-vars ,name) (list-ref args 0))))]
             [(= (length args) 2)
              (let ([name (make-sym)])
                `(let ([,name ,(compile-L5e func bound-ids)])
                   ((closure-proc ,name) (closure-vars ,name) (list-ref args 0) (list-ref args 1))))]
             [else
              (let* ([sym (make-sym)]
                     [lab (make-lab sym)])
                (begin (add-func-tup lab args (free-ids-sub func args))
                       `((closure-proc ,sym) (closure-vars ,sym)
                                             (new-tuple (map (λ (element)
                                                               element)
                                                             args)))))]))
    (else
     (a-l5e))))

;; add-func-tup
(define (add-func-tup lab args free-vars body)
  (set! func-list (append func-list
                          (list lab (cons 'vars-tup 'args-tup)
                                (let ([t2-list 
                                       (let ([t-list body])
                                         (for ([i (in-range (- (length free-vars) 1) -1 -1)])
                                           (set! t-list `(let ([,(list-ref free-vars i) (aref vars-tup ,i)]) ,t-list))))])
                                  (for ([j (in-range (- (length args) 1) -1 -1)])
                                    (set! t2-list `(let ([,(list-ref args j) (aref args-tup ,j)]) ,t2-list))))))))

;; add-func
(define (add-func lab args free-vars body)
  (set! func-list (append func-list
                          (list lab (cons 'vars-tup args)
                                (let ([t-list body])
                                  (for ([i (in-range (- (length free-vars) 1) -1 -1)])
                                    (set! t-list `(let ([,(list-ref free-vars i) (aref vars-tup ,i)]) ,t-list))))))))

;; make-lab : sym -> lab
(define (make-lab var)
  (string->symbol (string-append ":" (symbol->string var))))

;; ret-count : void -> number
(define (make-count)
  (set! counter (add1 counter))
  counter)

;; make-sym : void -> sym
(define (make-sym)
  (string->symbol (string-append "new-func-var_"(number->string (make-count)))))

;; replace : L4e symbol symbol -> L4e
(define (replace sexp find-var repl-var)
  (cond
    [(equal? find-var sexp) repl-var]
    [(pair? sexp) (cons (replace (car sexp) find-var repl-var)
                        (replace (cdr sexp) find-var repl-var))]
    [else sexp]))

; var?((closure-proc f) (closure-vars f) 1)
(define (var? e)
  (not (equal? #\: (string-ref (symbol->string e) 0))))

; val?
(define (val? e)
  (or (var? e)
      (number? e)))

(define prim-set (set 'print 'new-array 'aref 'aset 'alen))
(define biop-set (set '+ '- '* '< '<= '=))
(define pred-set (set 'number? 'a?))

(define (biop? e)
  (not (set-empty? (set-intersect (set e) biop-set))))
(define (prim-set? e)
  (not (set-empty? (set-intersect (set e) prim-set))))
(define (pred? e)
  (not (set-empty? (set-intersect (set e) pred-set))))
(define (prim? e)
  (or (biop? e)
      (pred? e)
      (prim-set? e)))

; the snozzberries taste like snozzberries
(define-type L5E
  (lambda-e (args (listof (listof var?)))
            (body L5E?))
  (var-e (x var?))
  (let-e (bind (listof (list var? L5E?)))
         (body L5E?))
  (letrec-e (bind (listof (list var? L5E?)))
            (body L5E?))
  (if-e (cond L5E?)
        (then L5E?)
        (else L5E?))
  (new-tuple-e (args (listof L5E?)))
  (begin-e (first L5E?)
           (second L5E?))
  (app-e (func L5E?)
         (args (listof L5E?)))
  (prim-e (op prim?))
  (num-e (n number?)))

; parse : sexp -> L5E
(define (parse sexp)
  (match sexp
    [`(lambda ,args ,body)
     (lambda-e args (parse body))]
    [`(,let ,bind ,body)
     (let-e bind (parse body))]
    [`(,letrec ,bind ,body)
     (letrec-e bind (parse body))]
    [`(if ,cond ,then ,else)
     (if-e (parse cond)
           (parse then)
           (parse else))]
    [`(new-tuple ,args ...)
     (new-tuple-e (foldl (λ (arg res)
                           (append (list arg) res))
                         '()
                         args))]
    [`(begin ,first ,second)
     (begin-e (parse first)
              (parse second))]
    [(? number? n)
     (num-e n)]
    [(? prim? p)
     (prim-e p)]
    [else
     (app-e (parse (car sexp))
            (foldl (λ (arg res)
                     (append (list arg) res))
                   '()
                   (second sexp)))]))

;; symbol<? : symbol symbol -> boolean
;; symbol ordering
(define (symbol<? a b)
  (string<? (symbol->string a) (symbol->string b)))

;; free-ids-sub : L5e, listof vars -> listof vars
(define (free-ids-sub a-l5e a-list)
  (type-case L5E a-l5e
    (lambda-e (args body)
              (free-ids-sub body (append a-list args)))
    (var-e (x)
           (if (not (member x a-list))
               (list x)
               '()))
    (let-e (bind body)
           (append (free-ids-sub body (append (list (first bind)) a-list))
                   (free-ids-sub (second bind) a-list)))
    (letrec-e (bind body)
              (append (free-ids-sub body (append (list (first bind)) a-list))
                      (free-ids-sub (second bind) a-list)))
    (if-e (cond then else)
          (append (free-ids-sub cond a-list)
                  (free-ids-sub then a-list)
                  (free-ids-sub else a-list)))
    (new-tuple-e (args)
                 (foldl (λ (arg res)
                          (append res (free-ids-sub arg a-list)))
                        '()
                        args))
    (begin-e (first second)
             (append (free-ids-sub first a-list)
                     (free-ids-sub second a-list)))
    (app-e (func args)
           (append (free-ids-sub func a-list)
                   (foldl (λ (arg res)
                            (append res (free-ids-sub arg a-list)))
                          '()
                          args)))
    (prim-e (op) '())
    (num-e (n) '())))

;; sort-uniq : list-of-symbols -> list-of-symbols
;; takes in a list-of-symbols and returns a sorted list with no duplicates
(define (sort-uniq a-symbol-list)
  (remove-duplicates (sort a-symbol-list symbol<?)))