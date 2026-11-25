(** Federer (1969), 4.1.24, p. 382: the
    attained ordinary flat minimum has a filling
    in the original F_(m+1,K). Compare it with
    one finite-mass flat decomposition in the same K;
    the four finite masses make their filling
    difference normal. Thus no enlarged support or
    finite M(T) premise is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed CurrentMassBasic
  CurrentFlatNorm CurrentFlatMinimum FlatCurrentsUP FlatCurrentClosure FlatCurrentFinite
  FlatCurrentBoundary CurrentFiniteMassFillingDifference FlatCurrentFiniteMassDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentAttainedFlatFilling.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Flat:=(fun d=>@is_flat_current_supported_in R h2 n d U hU K).
Local Notation Minimum:=(@is_current_flat_minimiser R h2 n m U hU K).

(** Source for [flat_current_minimiser_is_flat]: every
    attained minimum of an original flat current
    belongs to the original compact flat filling
    space, the final argument in 4.1.24, p. 382. *)
Theorem flat_current_minimiser_is_flat (T:C) (S:Next):
  Flat m T->Minimum T S->Flat m.+1 S.
Proof.
move=>hT hMinimum.
have[A0 [S0 [hA0Flat [hS0Flat [hA0Finite [hS0Finite hTEqual]]]]]]:=
  @flat_current_finite_mass_decomposition R h2 n m U hU K T hT.
have hFFinite:=@flat_current_supported_finite R h2 n m U hU K T hT.
have hCost:(M m (T-bd S)%R+M m.+1 S< +oo)%E by rewrite -hMinimum.2.1.
have hAFinite:(M m (T-bd S)%R< +oo)%E.
  exact:le_lt_trans (leeDl (M m (T-bd S))
    (@current_mass_nonnegative R h2 n m.+1 U hU S)) hCost.
have hSFinite:(M m.+1 S< +oo)%E.
  exact:le_lt_trans (leeDr (M m.+1 S)
    (@current_mass_nonnegative R h2 n m U hU (T-bd S))) hCost.
have hEqual:(T-bd S)+bd S=A0+bd S0 by rewrite subrK hTEqual.
have hDifferenceNormal:=@current_finite_filling_difference_normal R h2 n m U hU K
  (T-bd S) A0 S S0 hAFinite hA0Finite hSFinite hS0Finite hEqual hMinimum.1
  (@flat_current_supported_support R h2 n m.+1 U hU K S0 hS0Flat).
have hDifferenceFlat:=@supported_normal_current_is_flat R h2 n m.+1 U hU K
  (S-S0) hDifferenceNormal.
have hSum:(@flat_current_subspace R h2 n m.+1 U hU K) ((S-S0)+S0).
  exact:(@subspace_add R Next (@flat_current_subspace R h2 n m.+1 U hU K)
    (S-S0) S0 hDifferenceFlat hS0Flat).
by rewrite subrK in hSum.
Qed.

(** Source for [flat_current_attained_flat_filling]: the original
    final flat-filling minimum of 4.1.24, p. 382,
    with exact K, the full minimum property and both
    finite masses. M(T) may be infinite. This is
    the ordinary flat minimum; the integral minimum
    deferred to 4.2.18 is not asserted here. *)
Theorem flat_current_attained_flat_filling (T:C):
  Flat m T->exists S:Next,Flat m.+1 S /\Minimum T S /\
    Flat m (T-bd S) /\(M m.+1 S< +oo)%E /\(M m (T-bd S)%R< +oo)%E.
Proof.
move=>hT.
have[S hMinimum]:=@current_flat_minimum_attained R h2 n m U hU K T
  (@flat_current_supported_support R h2 n m U hU K T hT).
have hSFlat:=flat_current_minimiser_is_flat hT hMinimum.
have hBoundaryFlat:=@flat_current_boundary_supported R h2 n m U hU K S hSFlat.
have hResidualFlat:Flat m (T-bd S).
  exact:(@subspace_sub R C (@flat_current_subspace R h2 n m U hU K)
    T (bd S) hT hBoundaryFlat).
have hFFinite:=@flat_current_supported_finite R h2 n m U hU K T hT.
have hCost:(M m (T-bd S)%R+M m.+1 S< +oo)%E by rewrite -hMinimum.2.1.
exists S;split;first exact:hSFlat.
split;first exact:hMinimum.
split;first exact:hResidualFlat.
split.
- exact:le_lt_trans (leeDr (M m.+1 S)
    (@current_mass_nonnegative R h2 n m U hU (T-bd S))) hCost.
- exact:le_lt_trans (leeDl (M m (T-bd S))
    (@current_mass_nonnegative R h2 n m.+1 U hU S)) hCost.
Qed.
End FlatCurrentAttainedFlatFilling.
