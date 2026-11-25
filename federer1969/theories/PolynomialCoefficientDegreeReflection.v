(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: a faithful original coefficient map
    also reflects polynomial degree. Apply the
    existing coefficient-extension equation directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialDegreeUP PolynomialCoefficientMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_coefficient_map_degree_reflect]:
    the linear gcd descends with its original
    degree, supporting the classical simplicity
    argument in 3.4.8(8), p. 330. Faithful
    coefficient inclusion preserves each zero test. *)
Theorem polynomial_coefficient_map_degree_reflect (A C:comNzRingType) (B D:Type)
  (source:B->nat->A) (target:D->nat->C) (phi:{rmorphism A->C}) (M:B->D):
  is_polynomial_coefficient_map source target phi M ->injective phi ->
  forall P:B,forall d,is_polynomial_degree target (M P) d ->is_polynomial_degree source P d.
Proof.
move=>hM hInjective P d hDegree;split.
- move=>hZero;apply:hDegree.1;by rewrite hM hZero rmorph0.
- move=>i hi;apply:hInjective;by rewrite -(hM P i) hDegree.2 // rmorph0.
Qed.
