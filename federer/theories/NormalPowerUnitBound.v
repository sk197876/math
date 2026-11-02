(** Federer (1969), 1.8.2, p. 40: the scalar normal-form
    computation gives the factorial upper bound and its equality
    criterion on unit exterior vectors. Orthonormality and coefficients
    in [0,1] are the only geometric hypotheses in this supporting step. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates InnerProductUP InnerPolarity
  InnerNorm InnerCauchy InnerNormInequalities InnerExterior InnerExteriorPositivity ExteriorNorm
  OrthonormalFamilies SkewNormalFormUP PairedRealVectors TwoFormPowers
  NormalPowerPolarity WirtingerCoefficientProduct InnerUnitEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bound.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable k : nat.
Variables a b : 'I_k -> V.
Variable lambda : 'I_k -> R.
Hypothesis ho : orthonormal_family B (paired_family a b).
Hypotheses (h0 : forall i, 0 <= lambda i) (h1 : forall i, lambda i <= 1).
Local Notation eta := (paired_real_vector a b).
Local Notation phi := (\sum_j lambda j *: form_wedge h2 (scalar_bilinear R)
  (inner_polarity hB (a j)) (inner_polarity hB (b j))).
Variable x : exterior_power V (k+k).
Hypothesis hx : exterior_norm h2 hB x = 1.
Local Notation delta := (exterior_inner_form h2 hB x eta).

(** Source for [normal_volume_inner_bound]: Federer 1.8.2,
    p. 40, the unit vector paired with the unit normal-form volume
    has inner product at most one. In top dimension this is delta=+/-1. *)
Lemma normal_volume_inner_bound : delta <= 1.
Proof.
have hh := inner_cauchy_upper (@exterior_inner_productP R h2 V B hB (k+k)) x eta.
change (is_true (delta <= exterior_norm h2 hB x * exterior_norm h2 hB eta)) in hh.
by rewrite hx (paired_orthonormal_vector_unit h2 hB ho) mul1r in hh.
Qed.

(** Source for [normal_power_pairing_computation]: Federer 1.8.2,
    p. 40, the pairing with the power is delta k! times the
    product of the normal-form coefficients. *)
Lemma normal_power_pairing_computation :
  pairing x (two_form_power h2 phi k) = (k`!%:R : R) * (delta * \prod_i lambda i).
Proof.
rewrite normal_two_form_power_polarity (bilZr (@pairing_bilinear R V R^o (k+k))).
change (((k`!%:R : R) * \prod_i lambda i) * delta =
  (k`!%:R : R) * (delta * \prod_i lambda i)).
by rewrite -mulrA [(_ * delta)]mulrC.
Qed.

(** Source for [normal_two_form_unit_bound]: Federer 1.8.2,
    p. 40, the factorial upper bound after the normal-form reduction. *)
Theorem normal_two_form_unit_bound : pairing x (two_form_power h2 phi k) <= k`!%:R.
Proof.
rewrite normal_power_pairing_computation.
apply: ler_piMr; first exact: ler0n.
exact: (@wirtinger_signed_product_bound R (Finite.clone 'I_k _) lambda h0 h1
  delta normal_volume_inner_bound).
Qed.

(** Source for [normal_two_form_unit_equality]: Federer 1.8.2,
    p. 40, equality means the exterior vector is precisely the
    positive paired volume and all normal-form coefficients are one. *)
Theorem normal_two_form_unit_equality :
  pairing x (two_form_power h2 phi k) = k`!%:R <->
    x = eta /\ forall i, lambda i = 1.
Proof.
have hf : (k`!%:R : R) != 0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have he : delta = 1 <-> x = eta.
  exact: (@inner_unit_pair_equality R (exterior_power V (k+k))
    (@exterior_inner_form R h2 V B hB (k+k))
    (@exterior_inner_productP R h2 V B hB (k+k)) x eta hx
    (@paired_orthonormal_vector_unit R h2 V B hB k a b ho)).
rewrite normal_power_pairing_computation.
split.
- move=> hp.
  have hp' : delta * \prod_i lambda i = 1.
    apply: (mulfI hf); by rewrite mulr1.
  have [hd hl] := proj1
    (@wirtinger_signed_product_equality R (Finite.clone 'I_k _) lambda h0 h1
      delta normal_volume_inner_bound) hp'.
  split=> //; exact: (proj1 he hd).
- move=> [heq hl].
  have hd := proj2 he heq.
  have hp := proj2 (@wirtinger_coefficient_product_equality R (Finite.clone 'I_k _) lambda h0 h1) hl.
  by rewrite hd hp !mulr1.
Qed.
End Bound.
