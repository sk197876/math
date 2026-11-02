(** Federer (1969), 1.10.5, p. 48: the mass product inequality, now in all
    degrees for the dual-supremum interface. The scalar degree-zero cases
    are proved separately from the canonical identifications, rather than
    extending the unweighted infimum. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import AlgebraUP Bilinear GradedComponents SymmetricAlgebra
  SymmetricGrading SymmetricLowPowers SymmetricPowerProducts SymmetricFormIsomorphism
  RealNormUP SymmetricDegreeZeroPairing SymmetricMass SymmetricMassProductBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_degree_zero_value]: Federer 1.10.5,
    p. 48, supporting scalar multiplication case, using the
    degree-zero identification of 1.9.1, p. 41. *)
Lemma symmetric_degree_zero_value (K : fieldType) (V : lmodType K)
    (x : symmetric_power V 0) :
  component_val x = symmetric_zeroth_inverse V x *: symmetric_unit V.
Proof.
have hx := @symmetric_zeroth_tuple_scalar K V (symmetric_zeroth_inverse V x).
rewrite symmetric_zeroth_inverseK in hx.
have hh := congr1 (@component_val K (symmetric_space V) (symmetric_grading V) 0) hx.
change (component_val x = symmetric_zeroth_inverse V x *:
  component_val (symmetric_tuple_component ([tuple] : 0.-tuple V))) in hh.
by rewrite symmetric_tuple_componentE symmetric_word_nil in hh.
Qed.

(** Source for [symmetric_zeroth_product]: Federer 1.10.5,
    p. 48, multiplication by a zero-vector is scalar
    multiplication under the degree-zero identification. *)
Lemma symmetric_zeroth_product (K : fieldType) (V : lmodType K) q
    (x : symmetric_power V 0) (y : symmetric_power V q) :
  symmetric_reindex (add0n q) (symmetric_power_product x y) =
    (symmetric_zeroth_inverse V x : K) *: y.
Proof.
apply: val_inj.
change (component_val (symmetric_reindex (add0n q) (symmetric_power_product x y)) =
  symmetric_zeroth_inverse V x *: component_val y).
by rewrite symmetric_reindexE symmetric_power_productE symmetric_degree_zero_value
  (bilZl (symmetric_product_bilinear V)) symmetric_product_unitl.
Qed.

Section Bounds.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation mass := (symmetric_mass hN).

(** Source for [symmetric_mass_reindex]: Federer 1.10.5,
    p. 48, supporting bookkeeping: transporting across equal
    degree indices does not alter the mass. *)
Lemma symmetric_mass_reindex p q (h : p=q) (x : symmetric_power V p) :
  mass (symmetric_reindex h x) = mass x.
Proof. by case: q / h. Qed.

(** Source for [symmetric_mass_zeroth_product_left]: Federer
    1.10.5, p. 48, the product inequality is an equality
    when the first degree is zero. *)
Lemma symmetric_mass_zeroth_product_left q (x : symmetric_power V 0) (y : symmetric_power V q) :
  mass (symmetric_power_product x y) = mass x * mass y.
Proof.
rewrite -(symmetric_mass_reindex (add0n q) (symmetric_power_product x y))
  symmetric_zeroth_product symmetric_mass_scale symmetric_mass_degree_zero.
by [].
Qed.

(** Source for [symmetric_mass_zeroth_product_right]: Federer
    1.10.5, p. 48, the product inequality is an equality
    when the second degree is zero, by commutativity. *)
Lemma symmetric_mass_zeroth_product_right p (x : symmetric_power V p) (y : symmetric_power V 0) :
  mass (symmetric_power_product x y) = mass x * mass y.
Proof.
rewrite -(symmetric_mass_reindex (addnC p 0) (symmetric_power_product x y))
  symmetric_power_product_commute symmetric_mass_zeroth_product_left mulrC.
by [].
Qed.

(** Source for [symmetric_mass_product_bound]: Federer 1.10.5,
    p. 48, the displayed inequality ||xi eta|| <= ||xi|| ||eta||,
    including scalar factors and arbitrary ambient dimensions. *)
Theorem symmetric_mass_product_bound p q (x : symmetric_power V p) (y : symmetric_power V q) :
  mass (symmetric_power_product x y) <= mass x * mass y.
Proof.
case: p x=> [x|p x]; first by rewrite symmetric_mass_zeroth_product_left.
case: q y=> [y|q y]; first by rewrite symmetric_mass_zeroth_product_right.
have hp := ltn0Sn p; have hq := ltn0Sn q.
have hpq : (0<p.+1+q.+1)%N by [].
rewrite (@symmetric_mass_positive_degree R V N hN _ hpq)
  (@symmetric_mass_positive_degree R V N hN _ hp)
  (@symmetric_mass_positive_degree R V N hN _ hq).
exact: symmetric_projective_mass_product_bound.
Qed.
End Bounds.
