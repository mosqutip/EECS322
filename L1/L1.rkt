#lang plai
(require racket/string)
(require racket/file)

(define my-exp (call-with-input-file "x.L1" read))

(define-type L1
  [reg (name symbol?)]
  [label (name symbol?)]
  [move (lhs L1?)
        (rhs L1?)]
  [readmeme (dst L1?)
            (src L1?)
            (off L1?)]
  [writememe (dst L1?)
             (src L1?)
             (off L1?)]
  [pluse (lhs L1?)
         (rhs L1?)]
  [sube (lhs L1?)
        (rhs L1?)]
  [ande (lhs L1?)
        (rhs L1?)]
  [multe (lhs L1?)
         (rhs L1?)]
  [shiftle (lhs L1?)
           (rhs L1?)]
  [shiftre (lhs L1?)
           (rhs L1?)]
  [cmpe (dst L1?)
        (cond1 L1?)
        (op symbol?)
        (cond2 L1?)]
  [gotoe (label1 L1?)]
  [jumpe (cond1 L1?)
         (op symbol?)
         (cond2 L1?)
         (label1 L1?)
         (label2 L1?)]
  [imm (n number?)]
  [calle (u L1?)]
  [tailcalle (u L1?)]
  [returne]
  [printe (out L1?)]
  [alloce (a L1?)
          (b L1?)]
  [arrerre (a L1?)
           (b L1?)])

;; parse : sexp -> L1
(define (parse sexp)
  (cond
    [(number? sexp) (imm sexp)]
    [(pair? sexp)
     (cond
       [(list? (first sexp))
        (writememe (parse (third sexp))
                   (parse (second (first sexp)))
                   (parse (third (first sexp))))]
       [(and (eq? 3 (length sexp)) (list? (third sexp)))
        (case (first (third sexp))
          [(mem)
           (readmeme (parse (second (third sexp)))
                     (parse (first sexp))
                     (parse (third (third sexp))))]
          [(print)
           (printe (parse (second (third sexp))))]
          [(allocate)
           (alloce (parse (second (third sexp)))
                   (parse (third (third sexp))))]
          [(array-error)
           (arrerre (parse (second (third sexp)))
                    (parse (third (third sexp))))])]
       [(symbol=? 'cjump (first sexp))
        (jumpe (parse (second sexp))
               (third sexp)
               (parse (fourth sexp))
               (parse (fifth sexp))
               (parse (sixth sexp)))]
       [(symbol=? 'goto (first sexp))
        (gotoe (parse (second sexp)))]
       [(symbol=? 'call (first sexp))
        (calle (parse (second sexp)))]
       [(symbol=? 'tail-call (first sexp))
        (tailcalle (parse (second sexp)))]
       [(symbol=? 'return (first sexp))
        (returne)]
       [(and (eq? 5 (length sexp))
             (or (symbol=? '< (fourth sexp))
                 (symbol=? '<= (fourth sexp))
                 (symbol=? '= (fourth sexp))))
        (cmpe (parse (first sexp))
              (parse (third sexp))
              (fourth sexp)
              (parse (fifth sexp)))]
       [else
        (case (second sexp)
          [(+=)
           (pluse (parse (first sexp))
                  (parse (third sexp)))]
          [(-=)
           (sube (parse (first sexp))
                 (parse (third sexp)))]
          [(&=)
           (ande (parse (first sexp))
                 (parse (third sexp)))]
          [(*=)
           (multe (parse (first sexp))
                  (parse (third sexp)))]
          [(<-)
           (move (parse (first sexp))
                 (parse (third sexp)))]
          [(<<=)
           (shiftle (parse (first sexp))
                    (parse (third sexp)))]
          [(>>=)
           (shiftre (parse (first sexp))
                    (parse (third sexp)))])])]
    [else 
     (cond
       [(eq? #\: (string-ref (symbol->string sexp) 0))
        (label sexp)]
       [else
        (reg sexp)])]))

(define (apply-op a op b)
  (case op
    [(<) (< a b)]
    [(<=) (<= a b)]
    [(=) (= a b)]))

(define (evaluate-op op)
  (case op
    [(<) (string-append "setl ")]
    [(<=) (string-append "setle ")]
    [(=) (string-append "sete ")]))

(define (evaluate-negop op)
  (case op
    [(<) (string-append "setg ")]
    [(<=) (string-append "setge ")]
    [(=) (string-append "sete ")]))

(define (low-bits reg)
  (string-append "%" (substring reg 2 3) "l"))

(define (op-jmp op l1 l2)
  (case op
    [(<) (string-append "jl " l1 
                        "\njmp " l2)]
    [(<=) (string-append "jle " l1 
                         "\njmp " l2)]
    [(=) (string-append "je " l1 
                        "\njmp " l2)]))

(define (negop-jmp op l1 l2)
  (case op
    [(<) (string-append "jg " l1 
                        "\njmp " l2)]
    [(<=) (string-append "jge " l1 
                         "\njmp " l2)]
    [(=) (string-append "je " l1 
                        "\njmp " l2)]))

(define counter 0)

(define (new-lab)
  (set! counter (add1 counter))
  (string-append "_deflab" (number->string counter)))

(define (compile an-L1)
  (type-case L1 an-L1
    (reg (name) (string-append "%" (symbol->string name)))
    (label (name) (string-append "_" (substring (symbol->string name) 1)))
    (move (lhs rhs)
          (let* ([new-l (compile rhs)]
                 [new-r (compile lhs)])
            (when (eq? #\_ (string-ref new-l 0))
              (set! new-l (string-append "$" new-l)))
            (string-append "movl " new-l ", " new-r)))
    (readmeme (src dst off)
              (let* ([new-src (compile src)]
                     [new-dst (compile dst)]
                     [new-off (number->string (imm-n off))])
                (string-append "movl " new-off "(" new-src ")" ", " new-dst)))
    (writememe (src dst off)
               (let* ([new-src (compile src)]
                      [new-dst (compile dst)]
                      [new-off (number->string (imm-n off))])
                 (when (eq? #\_ (string-ref new-src 0))
                   (set! new-src (string-append "$" new-src)))
                 (string-append "movl " new-src ", " new-off "(" new-dst ")")))
    (pluse (lhs rhs)
           (let* ([new-l (compile rhs)]
                  [new-r (compile lhs)])
             (string-append "addl " new-l ", " new-r)))
    (sube (lhs rhs)
          (let * ([new-l (compile rhs)]
                  [new-r (compile lhs)])
            (string-append "subl " new-l ", " new-r)))
    (ande (lhs rhs)
          (let * ([new-l (compile rhs)]
                  [new-r (compile lhs)])
            (string-append "andl " new-l ", " new-r)))
    (multe (lhs rhs)
           (let * ([new-l (compile rhs)]
                   [new-r (compile lhs)])
             (string-append "imull " new-l ", " new-r)))
    (shiftle (lhs rhs)
             (let * ([new-l (compile rhs)]
                     [new-r (compile lhs)])
               (unless (eq? #\$ (string-ref new-l 0))
                 (set! new-l "%cl"))
               (string-append "sall " new-l ", " new-r)))
    (shiftre (lhs rhs)
             (let * ([new-l (compile rhs)]
                     [new-r (compile lhs)])
               (unless (eq? #\$ (string-ref new-l 0))
                 (set! new-l "%cl"))
               (string-append "sarl " new-l ", " new-r)))
    (cmpe (dest cond1 op cond2)
          (let * ([new-low-dest (low-bits (compile dest))]
                  [new-cond1 (compile cond2)]
                  [new-cond2 (compile cond1)]
                  [new-dest (compile dest)])
            (cond
              [(and (imm? cond1) (imm? cond2))
               (if (apply-op (imm-n cond1) op (imm-n cond2))
                   (string-append "mov $1, " new-dest)
                   (string-append "mov $0, " new-dest))]
              [(and (imm? cond1) (reg? cond2))
               (string-append "cmpl " new-cond2 ", " new-cond1 "\n"
                              (evaluate-negop op) new-low-dest "\n"
                              "movzbl " new-low-dest ", " new-dest)]
              [(or (and (reg? cond1) (imm? cond2))
                   (and (reg? cond1) (reg? cond2)))
               (string-append "cmpl " new-cond1 ", " new-cond2 "\n"
                              (evaluate-op op) new-low-dest "\n"
                              "movzbl " new-low-dest ", " new-dest)])))
    (gotoe (label1)
           (let ([new-label (compile label1)])
             (string-append "jmp " new-label)))
    (jumpe (cond1 op cond2 label1 label2)
           (cond
             [(and (imm? cond1) (imm? cond2))
              (if (apply-op (imm-n cond1) op (imm-n cond2))
                  (string-append "jmp " (compile label1))
                  (string-append "jmp " (compile label2)))]
             [(and (imm? cond1) (reg? cond2))
              (let* ([new-l (compile cond1)]
                     [new-r (compile cond2)])
                (string-append "cmpl " new-l ", " new-r "\n"
                               (negop-jmp op (compile label1)
                                       (compile label2))))]
             [(or (and (reg? cond1) (imm? cond2))
                  (and (reg? cond1) (reg? cond2)))
              (let* ([new-l (compile cond2)]
                     [new-r (compile cond1)])
                (string-append "cmpl " new-l ", " new-r "\n"
                               (op-jmp op (compile label1)
                                       (compile label2))))]))
    (imm (n) (string-append "$" (number->string n)))
    (calle (u) (let ([label (new-lab)])
                 (string-append "pushl $" label "\n"
                                "pushl %ebp\n"
                                "movl %esp, %ebp\n"
                                "jmp " (compile u) "\n"
                                label ":")))
    (tailcalle (u) (string-append "movl %ebp, %esp\n"
                                  "jmp " (compile u)))
    (printe (out) (string-append "pushl " (compile out) "\n"
                                 "call print\n"
                                 "addl $4, %esp"))
    (alloce (a b) (string-append "pushl " (compile b) "\n"
                                 "pushl " (compile a) "\n"
                                 "call allocate\n"
                                 "addl $8, %esp"))
    (arrerre (a b) (string-append "pushl " (compile b) "\n"
                                  "pushl " (compile a) "\n"
                                  "call print_error\n"
                                  "addl $8, %esp"))
    (returne () "movl %ebp, %esp\npopl %ebp\nret")))

; zero out file
(when (file-exists? "prog.temp")
  (delete-file "prog.temp"))
; then compile to it
(map (λ (chunk)
       (begin (map (λ (line)
                     (let ([a (compile (parse line))])
                       (with-output-to-file "prog.temp" #:exists 'append
                         (λ () (begin (when (eq? #\_ (string-ref a 0))
                                        (set! a (string-append a ":")))
                                      (display (string-append a "\n")))))))
                   chunk)
              (when (eq? chunk (first my-exp))
                (with-output-to-file "prog.temp" #:exists 'append
                  (λ () (display "ret\n"))))))
     my-exp)