(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: Rees elements whose coefficients lie in
    an original ideal form an actual ideal of the
    Rees ring. This supplies the filtered ideal in
    Artin–Rees; Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Corollary 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polynomial_coefficient_ideal_preimage]: all
    coefficient conditions define an ideal under the actual
    ring inclusion, supporting the cited Artin–Rees argument. *)
Theorem polynomial_coefficient_ideal_preimage (A B C:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (inclusion:{rmorphism C->B}) (J:set A):
  is_commutative_ideal J ->is_commutative_ideal (fun c:C=>forall n,J (coefficient (inclusion c) n)).
Proof.
move=>hJ;constructor.
- move=>n;rewrite rmorph0 (@polynomial_coefficient_zero A B embed variable coefficient hP).
  exact:commutative_ideal_zero hJ.
- move=>c d hc hd n;rewrite rmorphD (@polynomial_coefficient_add A B embed variable coefficient hP).
  exact:(@commutative_ideal_add A J hJ _ _ (hc n) (hd n)).
- move=>c hc n;rewrite rmorphN (@polynomial_coefficient_opp A B embed variable coefficient hP).
  exact:(@commutative_ideal_opp A J hJ _ (hc n)).
- move=>c d hd n;rewrite rmorphM (@polynomial_coefficient_multiply A B embed variable coefficient hP).
  apply:(big_ind J);first exact:commutative_ideal_zero hJ.
  + move=>a b ha hb;exact:(@commutative_ideal_add A J hJ a b ha hb).
  + move=>i _;exact:(@commutative_ideal_mul A J hJ _ _ (hd (n-i)%N)).
Qed.
