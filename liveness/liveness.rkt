#lang plai
(require racket/mpair)

#|----- File input functions -----|#
; define a list of input strings over which to iterate the spill function
(define input
  (first (file->list "L2l.input")))
#|----- End file input functions ----|#

#|----- List instantiation and helper functions -----|#
; lenght of the input function
(define len (length input))

; boolean flag for checking gen/kill correctness
(define changed 1)

; the gen list
(define gen-list
  (build-list len (λ (len) (box '()))))

; the kill list
(define kill-list
  (build-list len (λ (len) (box '()))))

; hash for the label -> index associations
(define label-hash
  (make-hash))

; hash for the special cases (cmp takes eax, ebx, ecx, edx, and
; shifting takes only ecx)
(define special-hash
  (make-hash))

(define cmp-regs (set 'esi 'edi))
(define shift-regs (set 'eax 'ebx 'edi 'edx 'esi))

; the initally killed vars (for comparison)
(define first-kill-list
  (build-list len (λ (len) (box '()))))

;; is-label? : symbol -> boolean
(define (is-label? s)
  (equal?
   (string-ref (symbol->string s) 0) #\:))

;; readable : symbol -> boolean
(define (readable? s)
  (and (not (number? s))
       (not (is-label? s))))
#|----- End list instantiation and helper functions -----|#

#|----- Begin main liveness matching function -----|#
;; gen-first : sexp -> listof gen
(define (gen-first sexp l)
  (for ([i (in-range l)])
    (match (list-ref sexp i)
      ; mem load
      [(list a '<- (list 'mem b _))
       (begin (set-box! (list-ref first-kill-list i) (list a))
              (when (readable? b)
                (set-box! (list-ref gen-list i) (list b))))]
      ; allocate, array-error
      [(list a '<- (list _ b c))
       (begin (set-box! (list-ref first-kill-list i) (list a 'eax 'ecx 'edx))
              (if (equal? b c)
                  (when (readable? b)
                    (set-box! (list-ref gen-list i) (list b)))
                  (begin (when (readable? b)
                           (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list b))))
                         (when (readable? c)
                           (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list c)))))))]
      ; print
      [(list a '<- (? list? b))
       (begin (set-box! (list-ref first-kill-list i) (list a 'eax 'ecx 'edx))
              (when (readable? (second b))
                (set-box! (list-ref gen-list i) (list (second b)))))]
      ; mem store
      [(list (list _ a _) '<- b)
       (if (equal? a b)
           (when (readable? a)
             (set-box! (list-ref gen-list i) (list a)))
           (begin (when (readable? a)
                    (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list a))))
                  (when (readable? b)
                    (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list b))))))]
      ; assignment
      [(list a '<- b)
       (begin (set-box! (list-ref first-kill-list i) (list a))
              (when (readable? b)
                (set-box! (list-ref gen-list i) (list b))))]
      ; sops
      [(or (list a '<<= b)
           (list a '>>= b))
       (begin (set-box! (list-ref first-kill-list i) (list a))
              (if (equal? a b)
                  (set-box! (list-ref gen-list i) (list a))
                  (if (readable? b)
                      (begin (set-box! (list-ref gen-list i) (list a b))
                             (hash-update! special-hash b
                                           (λ (val) (set-union val shift-regs))
                                           shift-regs))
                      (set-box! (list-ref gen-list i) (list a)))))]
      ; aops
      [(list a aop b)
       (begin (set-box! (list-ref first-kill-list i) (list a))
              (if (equal? a b)
                  (set-box! (list-ref gen-list i) (list a))
                  (if (readable? b)
                      (set-box! (list-ref gen-list i) (list a b))
                      (set-box! (list-ref gen-list i) (list a)))))]
      ; cmp
      [(list c '<- a _ b)
       (begin (set-box! (list-ref first-kill-list i) (list c))
              (hash-update! special-hash c
                            (λ (val) (set-union val cmp-regs))
                            cmp-regs)
              (if (equal? a b)
                  (when (readable? a)
                    (set-box! (list-ref gen-list i) (list a)))
                  (begin (when (readable? a)
                           (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list a))))
                         (when (readable? b)
                           (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list b)))))))]
      ; cjump
      [(list 'cjump a _ b _ _)
       (if (equal? a b)
           (when (readable? a)
             (set-box! (list-ref gen-list i) (list a)))
           (begin (when (readable? a)
                    (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list a))))
                  (when (readable? b)
                    (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list b))))))]
      ; call
      [(list 'call a)
       (begin
         (set-box! (list-ref gen-list i) (list 'eax 'ecx 'edx))
         (set-box! (list-ref first-kill-list i) (list 'eax 'ebx 'ecx 'edx))
         (when (readable? a)
           (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list a)))))]
      ; tail-call
      [(list 'tail-call a)
       (begin
         (set-box! (list-ref gen-list i) (list 'eax 'ecx 'edi 'edx 'esi))
         (when (readable? a)
           (set-box! (list-ref gen-list i) (append (unbox (list-ref gen-list i)) (list a)))))]
      ; return
      [(list 'return)
       (set-box! (list-ref gen-list i) (list 'eax 'edi 'esi))]
      ; label, goto label
      [else
       (cond
         [(list? (list-ref sexp i))
          (void)]
         [(is-label? (list-ref sexp i))
          (hash-set! label-hash (list-ref sexp i) i)]
         [else (void)])])))
#|----- End main liveness match function -----|#

#|----- Gen- and kill-list update helper functions -----|#
;; no-change-list (handles special cases)
(define no-change-list (list 'tail-call 'return 'array-error))
(define label-map-list (list 'cjump 'goto))

;; no-change : L2i -> boolean
(define (no-change inst) 
  (if (list? inst)
      (if (equal? (length inst) 3)
          (when (list? (third inst))
            (if (member (first (third inst)) no-change-list)
                #f
                #t))
          (if (member (first inst) no-change-list)
              #f
              #t))
      #t))

;; label-map : L2i -> boolean
(define (label-map inst)
  (if (list? inst)
      (if (member (first inst) label-map-list)
          #t
          #f)
      #f))

;; check-label-successor : L2i -> void
(define (check-label-successor inst i)
  (when (label-map inst)
    (if (equal? (first inst) 'goto)
        (let ([index (hash-ref label-hash (second inst))])
          (begin (set-box! (list-ref kill-list i)
                           (append (unbox (list-ref kill-list i))
                                   (unbox (list-ref gen-list index))))
                 (when (not (empty? (unbox (list-ref kill-list i))))
                   (set-box! (list-ref kill-list i)
                             (remove-duplicates (unbox (list-ref kill-list i)))))))
        (let* ([index1 (hash-ref label-hash (fifth inst))]
               [index2 (hash-ref label-hash (sixth inst))])
          (begin (set-box! (list-ref kill-list i)
                           (append (unbox (list-ref kill-list i))
                                   (unbox (list-ref gen-list index1))
                                   (unbox (list-ref gen-list index2))))
                 (when (not (empty? (unbox (list-ref kill-list i))))
                   (set-box! (list-ref kill-list i)
                             (remove-duplicates (unbox (list-ref kill-list i))))))))))

;; update-kill : void -> void
(define (update-kill)
  (for ([i (in-range (- (length gen-list) 1) -1 -1)])
    (if (label-map (list-ref input i))
        (check-label-successor (list-ref input i) i)
        (when (<= i (- (length gen-list) 2))
          (map (λ (x)
                 (when (no-change (list-ref input i))
                   (when (not (member x (unbox (list-ref kill-list i))))
                     (begin (set-box! (list-ref kill-list i)
                                      (append (list x)
                                              (unbox (list-ref kill-list i))))
                            (set! changed 1)))))
               (unbox (list-ref gen-list (+ i 1))))))))

;; update-gen : void -> void
(define (update-gen)
  (for ([i (in-range (- (length gen-list) 1) -1 -1)])
    (map (λ (x)
           (when (no-change (list-ref input i))
             (when (and (not (member x (unbox (list-ref first-kill-list i))))
                        (not (member x (unbox (list-ref gen-list i)))))
               (begin (set-box! (list-ref gen-list i) 
                                (append (list x)
                                        (unbox (list-ref gen-list i))))
                      (set! changed 1)))))
         (unbox (list-ref kill-list i)))))

;; symbol<? : symbol symbol -> boolean
(define (symbol<? a b)
  (string<? (symbol->string a) (symbol->string b)))

;; sort-lists : void -> void
(define (sort-lists)
  (for ([i (in-range len)])
    (set-box! (list-ref gen-list i) (sort (unbox (list-ref gen-list i)) symbol<?))
    (set-box! (list-ref kill-list i) (sort (unbox (list-ref kill-list i)) symbol<?))))

;; liveness : void -> void
(define (liveness)
  (gen-first input len)
  (check-loop)
  (sort-lists)
  (print-lists))

;; check-loop : void -> void
(define (check-loop)
  (if (equal? 0 changed)
      (void)
      (begin
        (set! changed 0)
        (update-kill)
        (update-gen)
        (check-loop))))
#|----- End gen- and kill-list update helper functions -----|#

#|----- File output functions -----|#
; output strings for the gen- and kill-lists
(define gen-output-string (open-output-string))
(define kill-output-string (open-output-string))

;; print-lists : void -> void
(define (print-lists)
  (for ([i (in-range len)])
    (display (unbox (list-ref gen-list i)) gen-output-string)
    (display (unbox (list-ref kill-list i)) kill-output-string)
    (unless (equal? i (- len 1))
      (display " " gen-output-string)
      (display " " kill-output-string))))

;; call the main function to perform the operation
(liveness)

;; Output the final instruction string to a file, in list form
(with-output-to-file "L2l.output" #:exists 'replace
  (λ () (begin
          (display (list
                    (list (string-append "in " (get-output-string gen-output-string)))
                    (list (string-append "out " (get-output-string kill-output-string))))))))
#|----- End file output functions -----|#