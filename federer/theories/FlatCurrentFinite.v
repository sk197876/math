(** Federer (1969), 4.1.12, p. 368: the
    original flat closure consists of finite-flat
    currents supported in K and includes every
    normal current supported in K. These facts
    follow from the earlier mass bound and actual
    dual support theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet CurrentFlatNorm CurrentFlatMassComparison CurrentMassSealed
  CompactRepresentedCurrentMass CurrentFlatFiniteSupport CurrentSupportGeometry
  FlatCurrentsUP NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentFinite.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU K).
Local Notation normalK := (@normal_currents_supported_in R h2 n U hU m K).
Local Notation support := (@current_support R h2 n U hU m).

(** Source for [supported_normal_current_flat_finite]: an
    original normal current supported in K has
    finite F_K, supporting the closure definition in
    Federer 4.1.12, p. 368. Its actual finite
    Radon mass bounds the original flat value. *)
Lemma supported_normal_current_flat_finite (T:C):normalK T->(F T < +oo)%E.
Proof.
move=>[hNormal hSupport].
have hMass:=@compact_represented_current_finite_mass R h2 n m U hU T hNormal.1.1 hNormal.2.
exact:le_lt_trans (@current_flat_norm_le_mass R h2 n m U hU K T hSupport) hMass.
Qed.

(** Source for [supported_normal_current_is_flat]: every
    original member of N_(m,K)(U) belongs to its
    F_K closure, Federer 4.1.12, p. 368.
    The current itself is an exact approximant. *)
Lemma supported_normal_current_is_flat (T:C):normalK T->flatK T.
Proof.
move=>hNormal epsilon hEpsilon;exists T;split;first exact:hNormal.
by rewrite subrr current_flat_norm_zero lte_fin.
Qed.

(** Source for [flat_current_supported_finite]: every
    original member of F_(m,K)(U) has finite F_K,
    supporting its completeness in Federer 4.1.12,
    p. 368. One normal approximant and the
    previously proved finite-flat vector-space laws suffice. *)
Theorem flat_current_supported_finite (T:C):flatK T->(F T < +oo)%E.
Proof.
move=>hFlat.
have [S [hNormal hApprox]]:=@hFlat 1 ltr01.
have hS:=supported_normal_current_flat_finite hNormal.
have hDifference:(F ((T-S)%R) < +oo)%E:=lt_trans hApprox (ltry 1).
have h:=@current_flat_finite_linear_combination R h2 n m U hU K 1 (T-S) S hDifference hS.
by rewrite scale1r subrK in h.
Qed.

(** Source for [flat_current_supported_support]: the
    original flat closure F_(m,K)(U) retains support
    in K, Federer 4.1.12, p. 368. Apply the
    earlier finite-flat support theorem to the actual
    test action, without choosing a new representative. *)
Theorem flat_current_supported_support (T:C):flatK T->support T `<=` smooth_compact_carrier K.
Proof.
move=>hFlat.
exact:(@current_finite_flat_functional_support R h2 n m U hU K
  (@current_value R h2 n U hU m T) (flat_current_supported_finite hFlat)).
Qed.
End FlatCurrentFinite.
