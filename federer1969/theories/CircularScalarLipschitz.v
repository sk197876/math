(** Federer (1969), 3.3.19, pp. 302–304:
    the actual sealed scalar sine and cosine are
    nonexpanding. Prove this from their actual derivatives
    and the project's convex-domain differential bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialScalar NormedCurveDerivativeUP NormHigherCurveDerivativeUP
  NormDifferentialConvexBound InnerConvex RealCurveDerivativeUP RealTrigonometryUP
  CircularTrigonometryUP CircularTrigonometrySealed CircularSineOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Lipschitz.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_full_differential]: actual
    differential of the original sine parameter, supporting
    the circular boundary curve in 3.3.19,
    pp. 302–304. The two-sided scalar derivative
    gives the full-source differential by proved laws. *)
Lemma circular_sine_full_differential a:
  has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (fun _=>True) S a
    (@scalar_coefficient_linear_map R R^o (C a)).
Proof.
apply:(@norm_differential_real_source R R^o (fun t=>`|t|) (@scalar_absolute_value_norm R)
  (fun _=>True) S a _).2;split.
- exists 1;split;first exact:ltr01;by move=>h _.
- change (has_normed_curve_derivative (fun t:R^o=>`|t|) S a (1* C a)).
  rewrite mul1r scalar_normed_curve_derivative;exact:real_sine_derivative hb a.
Qed.

(** Source for [circular_sine_nonexpanding]: actual
    global scalar bound used for the original
    circular boundary parametrization in 3.3.19,
    pp. 302–304. No external calculus estimate
    or additional Lipschitz premise is used. *)
Lemma circular_sine_nonexpanding x y:`|S x-S y|<=`|x-y|.
Proof.
pose N:=fun t:R^o=>`|t|.
have hN:=scalar_absolute_value_norm R.
have hConvex:is_inner_convex (@setT R^o) by move=>u v _ _ t _ _.
have hD a:exists L:Hom R^o R^o,
    has_norm_differential N N (fun _=>True) S a L /\forall t,N (L t)<=1* N t.
  exists (@scalar_coefficient_linear_map R R^o (C a));split;first exact:circular_sine_full_differential.
  move=>t;change (is_true (`|t* C a|<=1*`|t|)).
  rewrite normrM mul1r -[leRHS]mulr1.
  exact:(ler_wpM2l (normr_ge0 t) (real_cosine_bound hb a)).
have hBound:=@norm_differential_convex_bound R R^o R^o N N hN hN
  setT setT S 1 hConvex ler01 (fun a _=>hD a) x y Logic.I Logic.I.
by rewrite mul1r in hBound.
Qed.

(** Source for [circular_cosine_nonexpanding]: actual
    cosine bound supporting the circular boundary curve
    in 3.3.19, pp. 302–304. Reflection
    reduces it to the proved original sine bound. *)
Lemma circular_cosine_nonexpanding x y:`|C x-C y|<=`|x-y|.
Proof.
have hReflection t:C t=S (p/2-t).
  have hh:=@circular_sine_reflected_cosine R (p/2-t).
  have hAngle:p/2-(p/2-t)=t by ring.
  by rewrite hAngle in hh.
rewrite !hReflection.
have hBound:=@circular_sine_nonexpanding (p/2-x) (p/2-y).
have hDifference:(p/2-x)-(p/2-y)= -(x-y) by ring.
by rewrite hDifference normrN in hBound.
Qed.
End Lipschitz.
