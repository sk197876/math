(** Federer (1969), 1.10.5, p. 48, the displayed submultiplicativity of
    mass. This is the positive-degree infimum version; arbitrary dimensions
    and input seminorms are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Bilinear GradedComponents RealNormUP
  RealSeminormOperations SymmetricAlgebra SymmetricGrading SymmetricPowerProducts
  SymmetricFormIsomorphism SymmetricDecompositionCosts SymmetricProjectiveMass
  SymmetricProjectiveSeminorm SymmetricProjectiveMaximality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_tuple_component_product]: Federer 1.10.5,
    p. 48, supporting multiplication of decomposable symmetric vectors:
    multiplication concatenates their lists of factors. *)
Lemma symmetric_tuple_component_product (K : fieldType) (V : lmodType K)
    p q (a : p.-tuple V) (b : q.-tuple V) :
  symmetric_power_product (symmetric_tuple_component a) (symmetric_tuple_component b) =
    symmetric_tuple_component [tuple of a++b].
Proof.
apply: val_inj.
change (component_val (symmetric_power_product (symmetric_tuple_component a) (symmetric_tuple_component b)) =
  component_val (symmetric_tuple_component [tuple of a++b])).
by rewrite symmetric_power_productE !symmetric_tuple_componentE symmetric_word_cat.
Qed.

(** Source for [symmetric_tuple_cost_cat]: Federer 1.10.5,
    p. 48, the cost of a concatenated tuple is the product
    of the costs of its two factor tuples. *)
Lemma symmetric_tuple_cost_cat (R : realFieldType) (V : lmodType R)
    (N : V -> R) p q (a : p.-tuple V) (b : q.-tuple V) :
  symmetric_tuple_cost N [tuple of a++b] = symmetric_tuple_cost N a * symmetric_tuple_cost N b.
Proof.
rewrite /symmetric_tuple_cost -(@big_tuple R 1 *%R V (p+q) [tuple of a++b] predT N) /= big_cat.
by rewrite (@big_tuple R 1 *%R V p a predT N) (@big_tuple R 1 *%R V q b predT N).
Qed.

Section ProductBound.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variables p q : nat.
Variables (hp : (0<p)%N) (hq : (0<q)%N) (hpq : (0<p+q)%N).
Local Notation Mp := (symmetric_projective_mass hN hp).
Local Notation Mq := (symmetric_projective_mass hN hq).
Local Notation M := (symmetric_projective_mass hN hpq).

(** Source for [symmetric_projective_mass_tuple_product_bound]:
    Federer 1.10.5, p. 48, supporting one-sided product estimate.
    Multiplication by one decomposable vector multiplies the infimum
    mass bound by at most the product of that vector's factor lengths. *)
Lemma symmetric_projective_mass_tuple_product_bound (a : p.-tuple V) (y : symmetric_power V q) :
  M (symmetric_power_product (symmetric_tuple_component a) y) <= symmetric_tuple_cost N a * Mq y.
Proof.
have hM := @symmetric_projective_mass_seminorm R V N hN (p+q) hpq.
have hlin := proj2 (@symmetric_power_product_bilinear R V p q) (symmetric_tuple_component a).
have hQ := @real_seminorm_linear_precompose R (symmetric_power V q) (symmetric_power V (p+q))
  M hM (fun z => symmetric_power_product (symmetric_tuple_component a) z) hlin.
apply: (@symmetric_projective_mass_maximal R V N hN q hq _ hQ
  (symmetric_tuple_cost N a) (symmetric_tuple_cost_nonnegative hN a) _ y).
move=> b; rewrite symmetric_tuple_component_product -symmetric_tuple_cost_cat.
exact: symmetric_projective_mass_tuple_bound.
Qed.

(** Source for [symmetric_projective_mass_product_bound]: Federer
    1.10.5, p. 48, the mass of a symmetric product is at most
    the product of the masses. Here both degrees are positive, so
    both factors use the finite-decomposition infimum. The displayed
    sum-degree positivity follows from either positive factor degree. *)
Theorem symmetric_projective_mass_product_bound (x : symmetric_power V p) (y : symmetric_power V q) :
  M (symmetric_power_product x y) <= Mp x * Mq y.
Proof.
have hM := @symmetric_projective_mass_seminorm R V N hN (p+q) hpq.
have hlin := proj1 (@symmetric_power_product_bilinear R V p q) y.
have hQ := @real_seminorm_linear_precompose R (symmetric_power V p) (symmetric_power V (p+q))
  M hM (fun z => symmetric_power_product z y) hlin.
rewrite mulrC.
apply: (@symmetric_projective_mass_maximal R V N hN p hp _ hQ
  (Mq y) (symmetric_projective_mass_nonnegative hN hq y) _ x).
move=> a; rewrite mulrC; exact: symmetric_projective_mass_tuple_product_bound.
Qed.
End ProductBound.
