(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: a coefficient Noetherian ring stabilises the
    bounded leading-coefficient ideals. This is the chain
    argument in the coefficient proof of Hilbert's theorem;
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 2, no. 10, Corollary 1, p. 184. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP
  NoetherianIdealMaximum PolynomialTruncatedLeadingUP PolynomialTruncatedLeadingExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [truncated_polynomial_leading_stabilizes]:
    the bounded coefficient ideals eventually coincide,
    the chain step of Hilbert's theorem; Bourbaki (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184,
    supporting the expanded ideal-closure proof for 3.4.8(5), p. 328. *)
Theorem truncated_polynomial_leading_stabilizes (A B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (I:set B) (hI:is_commutative_ideal I) (L:nat->set A)
    (hL:is_truncated_polynomial_leading_family coefficient I L):
  is_noetherian_commutative_ring A ->exists N,
    forall d,(N<=d)%N ->L d = L N.
Proof.
move=>hNoetherian.
pose F:set (set A):=fun J=>exists d,J=L d.
have hNonempty:exists J,F J by exists (L 0%N),0%N.
have hIdeal J:F J ->is_commutative_ideal J.
  move=>[d ->];exact:(@truncated_polynomial_leading_is_ideal A B embed variable coefficient hP I hI L hL d).
have [J [[N hJN] hMaximal]]:=@noetherian_ideal_family_maximum A F hNoetherian hNonempty hIdeal.
subst J;exists N=>d hND;apply/seteqP;split.
- apply:hMaximal.
  + by exists d.
  + exact:(@truncated_polynomial_leading_monotone A B embed variable coefficient hP I hI L hL N d hND).
- exact:(@truncated_polynomial_leading_monotone A B embed variable coefficient hP I hI L hL N d hND).
Qed.
