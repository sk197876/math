(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: successive original scalar maps
    compose through the independent evaluation and
    coefficient-map laws. These are connections between
    the existing polynomial interfaces of 3.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialEvaluationUP PolynomialCoefficientMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [polynomial_evaluation_after_ring_map]:
    original evaluation commutes with a further
    scalar homomorphism, supporting coefficient descent
    in 3.4.8(8), pp. 329–330. *)
Theorem polynomial_evaluation_after_ring_map (A B C D:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (phi:{rmorphism A->C}) (x:C)
  (E:{rmorphism B->C}) (T:{rmorphism C->D}):
  is_commutative_polynomial_evaluation embed variable phi x E ->
  is_commutative_polynomial_evaluation embed variable
    (GRing.RMorphism.clone A D (T \o phi) _) (T x)
    (GRing.RMorphism.clone B D (T \o E) _).
Proof.
move=>hE;constructor.
- move=>a;change (T (E (embed a)) = T (phi a)).
  by rewrite (polynomial_evaluation_constants hE).
- change (T (E variable) = T x);by rewrite (polynomial_evaluation_variable hE).
Qed.

(** Source for [polynomial_coefficient_map_composition]:
    successive original coefficient extensions act
    coefficient by coefficient, supporting the field
    comparisons in 3.4.8(8), pp. 329–330. *)
Theorem polynomial_coefficient_map_composition (A C F:comNzRingType) (B D G:Type)
  (source:B->nat->A) (middle:D->nat->C) (target:G->nat->F)
  (phi:{rmorphism A->C}) (psi:{rmorphism C->F}) (M:B->D) (N:D->G):
  is_polynomial_coefficient_map source middle phi M ->
  is_polynomial_coefficient_map middle target psi N ->
  is_polynomial_coefficient_map source target
    (GRing.RMorphism.clone A F (psi \o phi) _) (N \o M).
Proof. by move=>hM hN P i;rewrite /comp hN hM. Qed.

(** Source for [polynomial_evaluation_change_parameters]:
    pointwise equal original scalar maps and equal
    variable values give the same evaluation laws,
    supporting the commuting field diagrams of
    3.4.8(8), pp. 329–330. *)
Theorem polynomial_evaluation_change_parameters (A B C:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (phi psi:{rmorphism A->C}) (x y:C)
  (E:{rmorphism B->C}):
  is_commutative_polynomial_evaluation embed variable phi x E ->
  (forall a:A,phi a = psi a) ->x = y ->
  is_commutative_polynomial_evaluation embed variable psi y E.
Proof.
move=>hE hScalars hPoint;constructor.
- move=>a;by rewrite (polynomial_evaluation_constants hE) hScalars.
- by rewrite (polynomial_evaluation_variable hE) hPoint.
Qed.
