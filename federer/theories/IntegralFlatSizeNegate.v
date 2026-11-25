(** Federer (1969), 4.1.24, p. 382: the
    original integral flat size is even. Negating each
    actual same-K rectifiable pair preserves its cost
    and yields both infimum laws. The proof uses the
    independent specification and the public opaque value. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed
  CurrentFiniteMassNegation RectifiableCurrentApproximationUP RectifiableCurrentBasic
  RectifiableCurrentNegate IntegralCurrentClassesUP IntegralCurrentNegate
  IntegralFlatSizeUP IntegralFlatSizeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section IntegralFlatSizeNegate.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation Rect:=(fun d=>@is_rectifiable_current_supported_in R h2 n d U hU K).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Spec:=(@is_integral_flat_size R h2 n m U hU K).
Local Notation IntegralFlat:=(@is_integral_flat_current_supported_in R h2 n U hU m K).

(** Source for [integral_flat_size_negate_specification]: every
    original infimum value for T is the same value
    for -T, the evenness ingredient of the metric
    assertion in 4.1.24, p. 382. No attaining
    integral decomposition is assumed. *)
Theorem integral_flat_size_negate_specification (T:C) a:Spec T a->Spec (-T) a.
Proof.
move=>hSize;constructor.
- exact:integral_flat_size_nonnegative hSize.
- move=>A S hA hS hEqual.
  have hOriginal:T=(-A)+bd (-S).
    have h:=congr1 (fun Q:C=>-Q) hEqual.
    rewrite opprK opprD in h.
    by rewrite -[-S]sub0r (linB (hom_linear bd)) (lin0 (hom_linear bd)) sub0r.
  have hLower:=@integral_flat_size_lower R h2 n m U hU K T a hSize
    (-A) (-S) (rectifiable_current_negate hA) (rectifiable_current_negate hS) hOriginal.
  by rewrite (@current_finite_mass_negation R h2 n m U hU A
      (@rectifiable_current_finite_mass R h2 n m U hU K A hA))
    (@current_finite_mass_negation R h2 n m.+1 U hU S
      (@rectifiable_current_finite_mass R h2 n m.+1 U hU K S hS)) in hLower.
- move=>epsilon hEpsilon.
  have[A [S [hA [hS [hEqual hCost]]]]]:=
    @integral_flat_size_approximate R h2 n m U hU K T a hSize epsilon hEpsilon.
  exists (-A),(-S);split;first exact:rectifiable_current_negate hA.
  split;first exact:rectifiable_current_negate hS.
  split.
  + by rewrite -[-S]sub0r (linB (hom_linear bd)) (lin0 (hom_linear bd)) sub0r
      -opprD -hEqual.
  + by rewrite (@current_finite_mass_negation R h2 n m U hU A
      (@rectifiable_current_finite_mass R h2 n m U hU K A hA))
      (@current_finite_mass_negation R h2 n m.+1 U hU S
        (@rectifiable_current_finite_mass R h2 n m.+1 U hU K S hS)).
Qed.

(** Source for [integral_flat_size_even]: the actual original
    opaque size has exactly the evenness required for
    its additive-group metric, 4.1.24, p. 382.
    Arbitrary input membership witnesses give the same value. *)
Theorem integral_flat_size_even (T:C) (hT:IntegralFlat T) (hNeg:IntegralFlat (-T)):
  @IntegralFlatSize.value R h2 n m U hU K (-T) hNeg=
    @IntegralFlatSize.value R h2 n m U hU K T hT.
Proof.
apply:(@integral_flat_size_unique R h2 n m U hU K (-T)).
- exact:(@IntegralFlatSize.laws R h2 n m U hU K (-T) hNeg).
- exact:integral_flat_size_negate_specification
    (@IntegralFlatSize.laws R h2 n m U hU K T hT).
Qed.
End IntegralFlatSizeNegate.
