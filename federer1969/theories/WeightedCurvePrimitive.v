(** Federer (1969), 3.1.11, p. 220:
    telescoping primitive for the repeated integration-by-parts
    proof of the one-variable Taylor formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialArithmetic NormHigherCurveDerivativeUP
  ScalarCoefficientLinearAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_curve_primitive]:
    the finite sum of weighted successive derivatives
    used to telescope the integration-by-parts calculation
    in Federer 3.1.11, p. 220. The weights
    are supplied through their derivative laws below. *)
Definition weighted_curve_primitive (R : realType) (Y : lmodType R)
    (W : nat->R->R) (F : nat->R->Y) (k : nat) (t : R) : Y :=
  \sum_(i < k.+1) W i t*:F i t.

(** Source for [weighted_curve_primitive_successor]:
    splitting off the last term of the finite
    Taylor primitive, a supporting identity for
    Federer 3.1.11, p. 220. *)
Lemma weighted_curve_primitive_successor (R : realType) (Y : lmodType R)
    (W : nat->R->R) (F : nat->R->Y) k t :
  weighted_curve_primitive W F k.+1 t=
    weighted_curve_primitive W F k t+W k.+1 t*:F k.+1 t.
Proof. by rewrite /weighted_curve_primitive big_ord_recr. Qed.

(** Source for [weighted_curve_primitive_derivative]:
    derivative of the telescoping integration-by-parts
    primitive in Federer 3.1.11, p. 220.
    Only the finite derivative chain through the
    requested order is assumed. *)
Theorem weighted_curve_primitive_derivative (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (W : nat->R->R) (F : nat->R->Y) k :
  (forall t, A t -> W 0%N t= 1) ->
  (forall i, (i<=k)%N -> forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|) NY A (F i) a
      (scalar_coefficient_linear_map (F i.+1 a))) ->
  (forall i, (i<k)%N -> forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|)
      (fun t : R^o=>`|t|) A (W i.+1) a
      (@scalar_coefficient_linear_map R R^o (-W i a))) ->
  forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|) NY A
      (weighted_curve_primitive W F k) a
      (scalar_coefficient_linear_map (W k a*:F k.+1 a)).
Proof.
move=> hW0; elim: k=> [|k ih] hF hW a ha.
- rewrite (hW0 a ha) scale1r.
  apply: (norm_differential_domain_agreement (@scalar_absolute_value_norm R)
    _ (hF 0%N (leqnn _) a ha)).
  by move=> t ht; rewrite /weighted_curve_primitive big_ord1 (hW0 t ht) scale1r.
- have hd := ih (fun i hi=>hF i (leq_trans hi (leqnSn _)))
    (fun i hi=>hW i (ltn_trans hi (ltnSn _))) a ha.
  have hp := norm_curve_scalar_product hNY
    (hW k (ltnSn _) a ha) (hF k.+1 (leqnn _) a ha).
  have hs := norm_differential_add hNY hd hp.
  rewrite -scalar_coefficient_linear_add in hs.
  have hc : W k a*:F k.+1 a+
      ((-W k a)*:F k.+1 a+W k.+1 a*:F k.+2 a)=
      W k.+1 a*:F k.+2 a.
    by rewrite scaleNr addrA subrr add0r.
  rewrite hc in hs.
  apply: (norm_differential_domain_agreement (@scalar_absolute_value_norm R) _ hs).
  by move=> t ht; rewrite weighted_curve_primitive_successor.
Qed.

(** Source for [weighted_curve_primitive_endpoint]:
    at the upper endpoint the positive-order Taylor
    weights vanish, leaving f(1), as used in
    Federer 3.1.11, p. 220. *)
Lemma weighted_curve_primitive_endpoint (R : realType) (Y : lmodType R)
    (W : nat->R->R) (F : nat->R->Y) k b :
  W 0%N b= 1 -> (forall i, W i.+1 b= 0) ->
  weighted_curve_primitive W F k b=F 0%N b.
Proof.
move=> h0 hs; elim: k=> [|k ih].
- by rewrite /weighted_curve_primitive big_ord1 h0 scale1r.
- by rewrite weighted_curve_primitive_successor ih hs scale0r addr0.
Qed.
