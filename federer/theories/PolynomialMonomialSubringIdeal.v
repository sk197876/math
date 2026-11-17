(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: a subring containing the original constants
    determines an ideal of coefficients at each monomial
    degree. This supports finite generation of the Rees
    ring in Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [monomial_subring_coefficient_ideal]: original
    coefficients whose fixed-degree monomials lie in the
    subring form an ideal, supporting the cited Lemma 1. *)
Lemma monomial_subring_coefficient_ideal (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (T:set B) d:
  is_commutative_subring T ->(forall a:A,T (embed a)) ->
  is_commutative_ideal (fun a:A=>T (embed a*variable^+d)).
Proof.
move=>hT hConstants;constructor.
- rewrite rmorph0 mul0r;exact:commutative_subring_zero hT.
- move=>a b ha hb;rewrite rmorphD mulrDl.
  exact:(@commutative_subring_add B T hT _ _ ha hb).
- move=>a ha;rewrite rmorphN mulNr.
  exact:(@commutative_subring_opp B T hT _ ha).
- move=>a b hb;rewrite rmorphM -mulrA.
  exact:(@commutative_subring_multiply B T hT (embed a) (embed b*variable^+d) (hConstants a) hb).
Qed.

(** Source for [polynomial_monomial_multiply]: multiplying
    original monomials multiplies their coefficients and
    adds their degrees, supporting the cited Rees-ring Lemma 1. *)
Lemma polynomial_monomial_multiply (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (a b:A) m n:
  (embed a*variable^+m)*(embed b*variable^+n)=embed (a*b)*variable^+(m+n)%N.
Proof. by rewrite rmorphM exprD mulrACA. Qed.
