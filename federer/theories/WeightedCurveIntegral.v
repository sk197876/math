(** Federer (1969), 3.1.11, p. 220:
    the integral identity obtained from the finite
    Taylor primitive. The integral is an actual
    norm limit of tagged sums in the given target. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP
  NormHigherCurveDerivativeUP NormedStieltjesUP NormedCurveFundamentalTheorem
  NormClassZeroScalarProduct WeightedCurvePrimitive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_curve_integral]:
    the repeated integration-by-parts calculation
    in Federer 3.1.11, p. 220, before
    substituting the factorial polynomial weights.
    Its endpoint difference proves existence of the
    required vector integral without completing Y. *)
Theorem weighted_curve_integral (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (W : nat->R->R) (F : nat->R->Y) k :
  (forall t, 0<=t<= 1 -> A t) ->
  (forall t, A t -> W 0%N t= 1) ->
  (forall i, W i.+1 1= 0) ->
  (forall i, (i<=k)%N -> forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|) NY A (F i) a
      (scalar_coefficient_linear_map (F i.+1 a))) ->
  (forall i, (i<k)%N -> forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|)
      (fun t : R^o=>`|t|) A (W i.+1) a
      (@scalar_coefficient_linear_map R R^o (-W i a))) ->
  norm_class_zero (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) A (W k) ->
  norm_class_zero (fun t : R^o=>`|t|) NY A (F k.+1) ->
  has_normed_stieltjes_integral NY
    (fun t=>W k t*:F k.+1 t) (fun t=>t) 0 1
    (F 0%N 1-weighted_curve_primitive W F k 0).
Proof.
move=> hA hW0 hW1 hF hW hcW hcF.
have hD := weighted_curve_primitive_derivative hNY hW0 hF hW.
have hcont := norm_class_zero_scalar_product hNY hcW hcF.
have hi := normed_curve_fundamental_theorem hNY ler01 hA hD hcont.
have hA1 : A 1 by apply: hA; rewrite ler01 lexx.
by rewrite (@weighted_curve_primitive_endpoint R Y W F k 1 (hW0 1 hA1) hW1) in hi.
Qed.
