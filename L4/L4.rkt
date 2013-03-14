#lang plai

; maybe-let: L3-d (val -> L3-e) -> L3-e
(define (maybe-let d f)
  (if (val? d)
      (f d)
      (let ([x (fresh-var)])
        `(let ([,x ,d])
           ,(f x)))))


; fresh-var: void -> symbol
(define (fresh-var)
  (string->symbol (string-append
                   "L4_"
                   (number->string (make-count)))))

; make-count: void -> number
(define (make-count)
  (begin (set! counter (add1 counter))
         counter))

(define counter -1)

; norm: L4-e -> L3-e
(define (norm e)
  (find e (no-ctxt)))

; var? sexp -> bool
(define (var? e)
  (and (not (label? e))
       (symbol? e)))

; label? sexp -> bool
(define (label? e)
  (if (symbol? e)
      (equal? #\: (string-ref (symbol->string e) 0))
      #f))

; val? sexp -> bool
(define (val? e)
  (or (var? e)
      (number? e)
      (label? e)))

; lists
(define pred-set (set 'a? 'number?))
(define biop-set (set '+ '- '* '< '<= '=))

(define (biop? e)
  (not (set-empty? (set-intersect (set e) biop-set))))
(define (pred? e)
  (not (set-empty? (set-intersect (set e) pred-set))))

; L4-e? sexp -> bool
; checks if an expression is a valid L4-e
(define (L4-e? e)
  (match e
    [(or `(,(? L4-e?) (,(? label?) (,(? var?) ...) ,(? L4-e?)) ...)
         `(let ([(? var?) (? L4-e?)]) (? L4-e?))
         `(if ,(? L4-e?)
              ,(? L4-e?)
              ,(? L4-e?))
         `(,(? L4-e?) ,(? L4-e?) ...)
         `(new-array ,(? L4-e?)
                     ,(? L4-e?))
         `(new-tuple ,(? L4-e?) ...)
         `(aref ,(? L4-e?)
                ,(? L4-e?))
         `(aset ,(? L4-e?)
                ,(? L4-e?)
                ,(? L4-e?))
         `(alen ,(? L4-e?))
         `(begin ,(? L4-e?) 
                 ,(? L4-e?))
         `(print ,(? L4-e?))
         `(make-closure ,(? L4-e?) 
                        ,(? L4-e?))
         `(closure-proc ,(? L4-e?))
         `(closure-vars ,(? L4-e?))
         `(,(? biop?) ,(? L4-e?) 
                      ,(? L4-e?))
         `(,(? pred?) ,(? L4-e?))
         (? val?))
     #t]
    [else
     #f]))

; context
(define-type context
  [let-ctxt (x var?)
            (b L4-e?)
            (k context?)]
  [if-ctxt (t L4-e?)
           (e L4-e?)
           (k context?)]
  [fun-ctxt (a (listof L4-e?))
            (k context?)]
  [arg-ctxt (f val?)
            (a-done (listof L4-e?))
            (a-todo (listof L4-e?))
            (k context?)]
  [no-ctxt])

; find: L4-e context -> L3-e
(define (find e k)
  (match e
    #;[`(,(? label? l) ,(? (listof var?) args) ,(? list? body))
       `(,l ,args ,(find body (no-ctxt)))]
    [`(begin ,e1 ,e2)
     (find `(let ([,(fresh-var) ,e1]) ,e2) k)]
    [`(let ([,x ,r]) ,b)
     (find r (let-ctxt x b k))]
    [`(if ,c ,t ,e)
     (find c (if-ctxt t e k))]
    [`(,(? pred? p) ,e1)
     (find p (fun-ctxt `(,e1) k))]
    [`(,(? biop? b) ,e1 ,e2)
     (find b (fun-ctxt `(,e1 ,e2) k))]
    [`(closure-vars ,e1)
     (find 'closure-vars (fun-ctxt `(,e1) k))]
    [`(closure-proc ,e1)
     (find 'closure-proc (fun-ctxt  `(,e1)k))]
    [`(make-closure ,l ,e1)
     (find 'make-closure (fun-ctxt `(,l ,e1) k))]
    [`(print ,e1)
     (find 'print (fun-ctxt `(,e1) k))]
    [`(alen ,e1)
     (find 'alen (fun-ctxt `(,e1) k))]
    [`(aset ,e1 ,e2 ,e3)
     (find 'aset (fun-ctxt `(,e1 ,e2 ,e3) k))]
    [`(aref ,e1 ,e2)
     (find 'aref (fun-ctxt `(,e1 ,e2) k))]
    [`(new-array ,l ,v)
     (find 'new-array (fun-ctxt `(,l ,v) k))]
    [`(new-tuple ,v ...)
     (find 'new-tuple (fun-ctxt v k))]
    [`(,f ,a ...)
     (find f (fun-ctxt a k))]
    [(? val?)
     (fill e k)]))

; fill: L3-d context -> L3-e
(define (fill d k)
  (type-case context k
    [let-ctxt 
     (x b k)
     `(let ([,x ,d])
        ,(find b k))]
    [if-ctxt 
     (t e k)
     (maybe-let d
                (λ (v)
                  `(if ,v
                       ,(find t k)
                       ,(find e k))))]
    [fun-ctxt 
     (a k)
     (if (empty? a)
         (maybe-let d
                    (λ (v)
                      (fill `(,v) k)))
         (maybe-let d
                    (λ (v)
                      (find (first a)
                            (arg-ctxt v
                                      '()
                                      (rest a)
                                      k)))))]
    [arg-ctxt 
     (f a-done a-todo k)
     (if (= 0 (length a-todo))
         (maybe-let d
                    (λ (v)
                      (fill (append `(,f) a-done (list v)) k)))
         (maybe-let d
                    (λ (v)
                      (find (first a-todo)
                            (arg-ctxt f
                                      (append a-done (list v))
                                      (rest a-todo)
                                      k)))))]
    [no-ctxt () d]))

;; FILE I/O
(define input (first (file->list "L4.input")))
#;(define (compile L4e) 
  (with-output-to-file "L4.output" #:exists 'replace
    (λ () (begin (pretty-display (norm (first L4e)))
                 (when (not (empty? L4e))
                   (pretty-display (map (λ (fae)
                                          `(,(first fae)
                                            ,(second fae)
                                            ,(norm (third fae))))
                                        (rest L4e))))))))

(define (compile L4e) 
  (with-output-to-file "L4.output" #:exists 'replace
    (λ () (let ([func_start (norm (first L4e))])
            (if (not (empty? L4e))
                (pretty-display (cons func_start
                                      (map (λ (fae)
                                             `(,(first fae)
                                               ,(second fae)
                                               ,(norm (third fae))))
                                           (rest L4e))))
                (pretty-display func_start))))))

(compile input)