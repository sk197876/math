(** Federer (1969), 4.1.24, p. 382: the ordinary
    flat norm is bounded by the original integral flat
    infimum. Hence the new size separates actual currents.
    Compare the original same-K rectifiable decompositions
    with the previously proved flat minimum and finite
    dual test bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentEvaluation CurrentBoundary
  CurrentMassSealed CurrentMassFiniteAlgebra CurrentFlatNorm
  CurrentFlatDualSeminormBasic CurrentFlatMassComparison FlatCurrentFinite
  RectifiableCurrentApproximationUP RectifiableCurrentBasic RectifiableCurrentWitnesses
  IntegralCurrentClassesUP IntegralCurrentInclusions IntegralFlatSizeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section IntegralFlatSizeComparison.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation Flat:=(@current_flat_norm R h2 n m U hU K).
Local Notation Spec:=(@is_integral_flat_size R h2 n m U hU K).
Local Notation IntegralFlat:=(@is_integral_flat_current_supported_in R h2 n U hU m K).

(** Source for [ordinary_flat_le_integral_flat_size]: every
    original same-K rectifiable decomposition is an admissible
    ordinary flat decomposition, Federer 4.1.24, p. 382.
    Taking the infimum preserves the sharp coefficient one. *)
Theorem ordinary_flat_le_integral_flat_size (T:C) a:
  IntegralFlat T->Spec T a->(Flat T<=a%:E)%E.
Proof.
move=>hT hSize.
have hFlat:=@integral_flat_current_is_flat_supported R h2 n U hU K m T hT.
have hSupport:=@flat_current_supported_support R h2 n m U hU K T hFlat.
have hFinite:=@flat_current_supported_finite R h2 n m U hU K T hFlat.
have[f [hf hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m T) hFinite.
have hLower:f<=a.
  apply:(@integral_flat_size_greatest_lower_bound R h2 n m U hU K T a hSize f).
  move=>A S hA hS hEqual.
  have hBound:=@current_flat_decomposition_lower_bound R h2 n m U hU K T S
    hSupport (@rectifiable_current_support R h2 n m.+1 U hU K S hS).
  have hResidual:T-@current_boundary R h2 n m U hU S=A.
    by rewrite hEqual addrK.
  by rewrite /current_flat_norm hResidual hValue in hBound.
by rewrite /current_flat_norm hValue lee_fin.
Qed.

(** Source for [integral_flat_size_definite]: zero original
    integral flat size forces the actual current to
    vanish, giving separation for the metric of
    4.1.24, p. 382. Use the earlier exact finite
    flat test bound rather than a replacement norm. *)
Theorem integral_flat_size_definite (T:C) a:
  IntegralFlat T->Spec T a->a=0->T=0.
Proof.
move=>hT hSize hZero.
have hUpper:=ordinary_flat_le_integral_flat_size hT hSize.
rewrite hZero in hUpper.
have hFlatZero:Flat T=0%E.
  apply/eqP;rewrite eq_le hUpper /=.
  exact:(@current_flat_dual_nonnegative R h2 n m U hU K
    (@current_value R h2 n U hU m T)).
apply:(@current_values_extensional R h2 n m U hU)=>psi.
rewrite (lin0 (hom_linear (@current_value R h2 n U hU m))) hom_zeroE.
have hBound:=@current_flat_dual_finite_bound R h2 n m U hU K
  (@current_value R h2 n U hU m T) 0 hFlatZero psi.
rewrite mul0r normr_le0 in hBound;apply/eqP;exact:hBound.
Qed.

(** Source for [integral_flat_size_zero_current]: the actual
    zero current has original integral flat size zero,
    Federer 4.1.24, p. 382. Its zero rectifiable
    decomposition works at every original K. *)
Theorem integral_flat_size_zero_current a:Spec (0:C) a->a=0.
Proof.
move=>hSize.
have hCurrent:=@rectifiable_current_zero R h2 n m U hU K.
have hFilling:=@rectifiable_current_zero R h2 n m.+1 U hU K.
have hEqual:(0:C)=0+@current_boundary R h2 n m U hU (0:Next).
  by rewrite (lin0 (hom_linear (@current_boundary R h2 n m U hU))) addr0.
have hLower:=@integral_flat_size_lower R h2 n m U hU K (0:C) a hSize
  0 0 hCurrent hFilling hEqual.
rewrite !current_mass_zero adde0 lee_fin in hLower.
apply/eqP;rewrite eq_le hLower /=;exact:(integral_flat_size_nonnegative hSize).
Qed.
End IntegralFlatSizeComparison.
