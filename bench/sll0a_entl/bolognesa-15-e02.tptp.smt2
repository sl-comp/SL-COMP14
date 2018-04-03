(set-logic QF_S)
(set-info :source |
A. Rybalchenko and J. A. Navarro Perez.
[Separation Logic + Superposition Calculus = Heap Theorem Prover]
[PLDI 2011]
http://navarroj.com/research/papers.html#pldi11
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random") 
(set-info :status unsat)
(set-info :version "2014-05-28")

(declare-sort Sll_t 0)

(declare-fun next () (Field Sll_t Sll_t))

(define-fun ls ((?in Sll_t) (?out Sll_t)) Space
(tospace (or (= ?in ?out)
(exists ((?u Sll_t))
(and (distinct ?in ?out) (tobool
(ssep (pto ?in (ref next ?u)) (ls ?u ?out)
)))))))

(declare-fun x0 () Sll_t)
(declare-fun x1 () Sll_t)
(declare-fun x2 () Sll_t)
(declare-fun x3 () Sll_t)
(declare-fun x4 () Sll_t)
(declare-fun x5 () Sll_t)
(declare-fun x6 () Sll_t)
(declare-fun x7 () Sll_t)
(declare-fun x8 () Sll_t)
(declare-fun x9 () Sll_t)
(declare-fun x10 () Sll_t)
(declare-fun x11 () Sll_t)
(declare-fun x12 () Sll_t)
(declare-fun x13 () Sll_t)
(declare-fun x14 () Sll_t)
(declare-fun x15 () Sll_t)
(declare-fun x16 () Sll_t)
(declare-fun x17 () Sll_t)
(declare-fun x18 () Sll_t)
(declare-fun x19 () Sll_t)
(assert
  (and 
    (= nil nil)
    (tobool 
	(ssep
		(ls  x11 x14) 
		
		(pto x4 (ref next x9)) 
		
		(pto x2 (ref next x5)) 
		
		(pto x3 (ref next x12)) 
		
		(ls  x14 x11) 
		
		(ls  x10 x13) 
		
		(pto x6 (ref next x2)) 
		
		(pto x15 (ref next x6)) 
		
		(pto x7 (ref next x5)) 
		
		(pto x1 (ref next x13)) 
		
		(pto x5 (ref next x1)) 
		
		(pto x13 (ref next x12)) 
		
		(pto x8 (ref next x12)) 
		
		(ls  x12 x5) 
		
		(ls  x9 x8) 
		emp
	) )
  )
)
(assert
  (not
        (tobool 
	(ssep
		(ls  x15 x6) 
		
		(ls  x10 x13) 
		
		(ls  x6 x2) 
		
		(ls  x3 x12) 
		
		(ls  x4 x9) 
		
		(ls  x2 x5) 
		
		(ls  x9 x8) 
		
		(ls  x13 x12) 
		
		(ls  x7 x5) 
		
		(ls  x8 x13) 
		
		(ls  x14 x11) 
		
		(ls  x11 x14) 
		emp
	) )
  ))

(check-sat)
