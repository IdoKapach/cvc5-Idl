(set-option :produce-models true)
(set-logic QF_IDL)
(set-info :source |Example for Formal Techniques Summer School May 23, 2016 by
Clark Barrett
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)

; COMMAND-LINE: --lang smt2
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun x () Int 0)
; EXPECT: (define-fun y () Int (- 1))
; EXPECT: (define-fun z () Int 1)
; EXPECT: (define-fun w () Int (- 2))
; EXPECT: )
; EXIT: 0

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (<= (- y x) (- 1)))
(assert (<= (- w x) (- 2)))
(assert (<= (- x w) 2))
(assert (<= (- z x) 3))
(assert (<= (- w z) (- 3)))
(check-sat)
(get-model)