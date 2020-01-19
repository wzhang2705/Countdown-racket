;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname countdowntestingfile) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #t)))
;;*************************************************
;;Wen Hui Zhang 20825781
;;CS 135 - Fall 2019
;;Assignment 10 - Problem 2
;;*************************************************

;; An Operator (Op) is (anyof '+ '- '* '/)
;; A Binary Expression Tree (BET) is one of:
;; * Nat
;; * (list Op BET BET)

;;part i of a)
;; (swap i j lst) produces lst with the elements at positions
;;     i and j swapped
;; swap: Nat Nat (listof X) -> (listof X)
;;     requires: i, j < (length lst)

(define (swap i j lst)
  (local [(define (swap/help i j lst i-val j-val)
  (cond [(empty? lst) empty]
        [(= i 0) (cons j-val (swap/help (sub1 i) (sub1 j) (rest lst) i-val j-val))]
        [(= j 0) (cons i-val (swap/help (sub1 i) (sub1 j) (rest lst) i-val j-val))]
        [else (cons (first lst) (swap/help (sub1 i) (sub1 j) (rest lst) i-val j-val))]))]
  (swap/help i j lst (list-ref lst i) (list-ref lst j))))

;;part ii
;;(generate-permutations lst) produces all
;;   possible permutations of lst.
;;generate-permutations: (listof X) -> (listof (listof X))

(define (generate-permutations lst)
  (cond [(empty? lst) (list empty)]
        [(= (length lst) 1) (list lst)]
        [(= (length lst) 2) (list lst (reverse lst))]
        [else
         (foldr append empty
                (map (lambda (x)
                       (map (lambda (a) (cons x a))
                            (generate-permutations (remove x lst)))) lst))]))

;; part iii      
;; (generate-tuples lst n) produces all tuples of length n of
;; elements in lst.
;; generate-tuples: (listof X) Nat -> (listof (listof X))
;;Examples:

(define (generate-tuples lst n)
  (cond [(empty? lst) empty]
        [(= n 0) (list empty)]
        [(= n 1) (cons (list (first lst)) (generate-tuples (rest lst) n))]
        [else (foldr append empty
                     (map (lambda (x)
                            (map (lambda (a) (cons x a))
                                 (generate-tuples lst (sub1 n)))) lst))]))

;;part iv
;;cross: consumes two lists lst1 and lst2 and produces every pair permutation
;;    of elements in lst1 and lst2
;;cross: (listof Any) (listof Any) -> (listof (list Any Any))
;;Examples:
             
(define (cross lst1 lst2)
  (foldr (lambda (c1 result)
           (append (map (lambda (c2)
                          (list c1 c2))
                        lst2)
                   result))
         empty lst1))

;;(create-bets nlon nloop) produces a list of all possible BET
;;    based off of nlon and nloop.
;;create-bets: (listof (listof Num)) (listof (listof Op)) ->
;;    (listof BET)
;;    requires: (length nlon) - (length nloop) = 1
;;Examples:

(define (create-bets nlon nloop)
  (local [(define (create-pairs i n)
            (cond [(= i n) empty]
                  [else (cons (list (- (sub1 n) i) i) (create-pairs (add1 i) n))]))
          (define (create-left-right-pairs n) (create-pairs 0 n))
          ;;create-tree-structure n takes a n, node count and produces all possible binary trees
          ;;    with the pairs of n
          (define (create-tree-structure n)
            (cond [(= n 0) (list empty)]
                  [else (local [(define pairs (create-left-right-pairs n))]
                          (map (lambda (a) (cons n a)) (create-trees pairs)))]))
          ;;create-trees takes a list of pairs of node-cnt and produces all subtrees of the node-cnt
          (define (create-trees pairs)
            (cond [(empty? pairs) empty]
                  [else (local [(define left (first (first pairs)))
                                (define right (second (first pairs)))]
                          (append (cross (create-tree-structure left) (create-tree-structure right))
                                  (create-trees (rest pairs))))]))
          ;;replace-vals takes a nlst, which is a binary tree, and ops, nums, list of ops and nums,
          ;;    and replaces the numbers in the nlst with the operators in ops, and the empty
          ;;    lists with numbers in nums.
          (define (replace-vals nlst ops nums i j)
            (cond [(empty? nlst) empty]
                  [(number? (first nlst)) (cons (list-ref ops j)
                                                (replace-vals (rest nlst) ops nums i (add1 j)))]
                  [(empty? (first nlst)) (cons (list-ref nums i)
                                               (replace-vals (rest nlst) ops nums (add1 i) j))]
                  [(cons? (first nlst)) (cons (replace-vals (first nlst) ops nums i j)
                                              (replace-vals (rest nlst) ops nums
                                                            (+ (add1 (first (first nlst))) i) (+ (first (first nlst)) j)))]))
          ;;create-some-bets takes a list of trees and list of operators, ops,
          ;;    and list of numbers, nums, and produces all bets from that list.
          (define (create-some-bets lst ops nums)
            (cond [(empty? lst) empty]
                  [else (cons (replace-vals (first lst) ops nums 0 0)
                              (create-some-bets (rest lst) ops nums))]))]
    (foldr append empty
           (map (lambda (x)
                  (create-some-bets (create-tree-structure (length (second x))) (second x) (first x)))
                (cross nlon nloop)))))

;;part v
;;evaluate-bets takes a list of BETs and a target number and produces list of bets
;;   that reaches that number. If any intermediate values are not natural numbers,
;;   that BET is not included in the result.
;;evaluate-bets: (listof BET) Nat -> (listof BET)

(define (evaluate-bets bets target)
  (local [;;(my-op op val1 val2) takes an operator function, op,
          ;;    and two values, val1 and val2, and evaluates with the operator.
          ;;    If either of val1 or val2 (or both) are false, produce false.
          (define (my-op op val1 val2)
            (cond [(or (false? val1) (false? val2)) false]
                  [else (op val1 val2)]))
          ;;(evaluate bet) takes one BET, bet, and evaluates it.
          (define (evaluate bet)
            (cond [(empty? bet) 0]
                  [(number? bet) bet]
                  [(symbol? (first bet)) (evaluate-sym (first bet)
                                                       (evaluate (second bet)) 
                                                       (evaluate (third bet)))]
                  [(number? (first bet)) (first bet)]))
          ;;(evaluate sym) takes the symbol and performs operation on the
          ;;    rest of BET
          (define (evaluate-sym op left right)
            (cond [(symbol=? op '*) (my-op * left right)]
                  [(symbol=? op '/) (cond [(equal? right 0) false]
                                          [(not (integer? (my-op / left right))) false]
                                          [else (my-op / left right)])]
                  [(symbol=? op '+) (my-op + left right)]
                  [(symbol=? op '-) (cond [(my-op > right left) false]
                                          [else (my-op - left right)])]))]
    (cond [(empty? bets) empty]
          [(false? (evaluate (first bets))) (evaluate-bets (rest bets) target)]
          [(= (evaluate (first bets)) target) (cons (first bets) (evaluate-bets (rest bets) target))]
          [else (evaluate-bets (rest bets) target)])))

;;part vi
;;(countdown-numbers lon target) produces a BET using the numbers in lon
;;    that evaluates to target, or false if no such BET exists.
(define (countdown-numbers lon target)
  (local [(define (generate-valid-bets lon target)
            (evaluate-bets (create-bets (generate-permutations lon)
                                        (generate-tuples '(+ - * /) (sub1 (length lon))))
                           target))]
    (cond [(empty? (generate-valid-bets lon target)) false]
          [else (first (generate-valid-bets lon target))])))

(create-bets '((8 6 4 2)) '((/ + -)))
