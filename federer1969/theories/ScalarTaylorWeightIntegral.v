(** Federer (1969), 3.1.11, p. 220:
    normalization of the factorial Taylor weights
    in the normed-vector integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP
  NormHigherCurveDerivativeUP NormedPrimitiveCell NormClassZeroArithmetic
  NormedStieltjesUP NormedStieltjesLaws NormedCurveFundamentalTheorem ScalarTaylorWeights.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_taylor_weight_integral_constant]:
    the integral of (1-t)^k/k! times
    a fixed vector is that vector divided by
    (k+1)!, the normalization used in
    Federer 3.1.11, p. 220. *)
Theorem scalar_taylor_weight_integral_constant (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (c : Y) k :
  has_normed_stieltjes_integral NY
    (fun t=>scalar_taylor_weight k t*:c) (fun t=>t) 0 1
    ((((k.+1)`!)%:R)^-1*:c).
Proof.
pose A := fun _ : R=>True.
have hA a (_ : A a) : norm_domain_interior (fun t : R^o=>`|t|) A a.
  by exists 1; split=> //; exact: ltr01.
have hc := norm_class_zero_scale (@scalar_absolute_value_norm R) (-1)
  (@scalar_taylor_weight_continuous R A k hA).
have hD a (ha : A a) :
    has_norm_differential (fun t : R^o=>`|t|)
      (fun t : R^o=>`|t|) A (scalar_taylor_weight k.+1) a
      (@scalar_coefficient_linear_map R R^o ((-1)*scalar_taylor_weight k a)).
  rewrite mulN1r; exact: scalar_taylor_weight_differential (hA a ha).
have hseg t (_ : 0<=t<= 1) : A t by [].
have hi := normed_curve_fundamental_theorem (@scalar_absolute_value_norm R)
  ler01 hseg hD hc.
rewrite scalar_taylor_weight_upper scalar_taylor_weight_lower sub0r in hi.
have hj := normed_stieltjes_integral_linear_image
  (scalar_coefficient_linear_bound hNY (-c)) hi.
change (has_normed_stieltjes_integral NY
  (fun t=>((-1)*scalar_taylor_weight k t)*:(-c)) (fun t=>t) 0 1
  ((-(((k.+1)`!)%:R)^-1)*:(-c))) in hj.
rewrite scaleNr scalerN opprK in hj.
apply: normed_stieltjes_integral_ext _ _ hj=>t //.
by rewrite mulN1r scaleNr scalerN opprK.
Qed.
