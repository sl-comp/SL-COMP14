(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort NLL_lvl1_t 0)
(declare-sort NLL_lvl2_t 0)

; 'next' selector of level 1
(declare-fun next1 () (Field NLL_lvl1_t NLL_lvl1_t))
; 'next' selector of level 2
(declare-fun next2 () (Field NLL_lvl2_t NLL_lvl2_t))
; the bridge from level 2 to level 1
(declare-fun down () (Field NLL_lvl2_t NLL_lvl1_t))

; singly-linked list
(define-fun lso ((?in NLL_lvl1_t) (?out NLL_lvl1_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u NLL_lvl1_t)) 
      (and (distinct ?in ?out) 
           (tobool (ssep
           (pto ?in (ref next1 ?u))
           (lso ?u ?out))
))))))

; singly-linked list of singly-linked lists
(define-fun nll ((?in NLL_lvl2_t) (?out NLL_lvl2_t) (?boundary NLL_lvl1_t))
  Space (tospace (or (= ?in ?out)
    (exists ((?u NLL_lvl2_t) (?Z1 NLL_lvl1_t)) 
      (and (distinct ?in ?out) 
           (tobool (ssep
           (pto ?in (sref (ref next2 ?u) (ref down ?Z1)))
           (lso ?Z1 ?boundary)
           (nll ?u ?out ?boundary))
))))))

(declare-fun x1 () NLL_lvl2_t)
(declare-fun x1_1 () NLL_lvl1_t)
(declare-fun x1_2 () NLL_lvl1_t)
(declare-fun x1_3 () NLL_lvl1_t)
(declare-fun x2 () NLL_lvl2_t)
(declare-fun x3 () NLL_lvl2_t)
(declare-fun x3_1 () NLL_lvl1_t)
(declare-fun x3_2 () NLL_lvl1_t)

;
; three unfoldings of nll(x1,nil,nil) with list segment in middle
; exp: unsat
;
(assert (tobool (ssep
  (pto x1 (sref
    (ref next2 x2)
    (ref down x1_1)))
  (pto x1_1 (ref next1 x1_2))
  (pto x1_2 (ref next1 x1_3))
  (pto x1_3 (ref next1 nil))
  (nll x2 x3 nil)
  (pto x3 (sref
    (ref next2 nil)
    (ref down x3_1)))
  (pto x3_1 (ref next1 x3_2))
  (pto x3_2 (ref next1 nil))
)))

(assert (not (tobool 
  (nll x1 nil nil)
)))

(check-sat)

