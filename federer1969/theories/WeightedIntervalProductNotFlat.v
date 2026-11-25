(** Federer (1969), 4.1.12, p. 369:
    the original flat T has nonflat
    Cartesian square. The original S times T
    is nonflat as well, because its
    boundary is T times T. These
    are the actual original examples, with no added hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentCartesianDomain CurrentSpaces
  CurrentCartesianProductSealed CurrentCartesianBoundaryFirstZero CurrentDegreeTransportIdentity CurrentBoundary
  FlatCurrentsUP FlatCurrentBoundary CurrentFlatUniformTestBound WeightedIntervalCurrentSealed WeightedIntervalCurrentLaws
  WeightedIntervalProductTests WeightedIntervalProductTestBounds WeightedIntervalProductAction HarmonicPrefixBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalProductNotFlat.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation AB := (@euclidean_cartesian_set R 1%N 1%N Full Full).
Local Notation hAB := (@current_cartesian_domain_open R 1%N 1%N Full Full hFull hFull).
Local Notation S := (@WeightedIntervalCurrent.value R h2).
Local Notation T := (@weighted_interval_boundary R h2).
Local Notation TT := (@CartesianCurrentProduct.value R h2 1%N 1%N 0%N 0%N Full Full hFull hFull T T).
Local Notation ST := (@CartesianCurrentProduct.value R h2 1%N 1%N 1%N 0%N Full Full hFull hFull S T).
Local Notation psi := (@weighted_interval_product_test R h2).

(** Source for [weighted_interval_boundary_square_not_flat]:
    the actual original T times T
    does not belong to F_0(R^2),
    as asserted in Federer 4.1.12,
    p. 369. Its harmonic actions
    contradict the original finite flat bound. *)
Theorem weighted_interval_boundary_square_not_flat:
  ~@is_flat_current R h2 (1+1)%N 0%N AB hAB TT.
Proof.
move=>hFlat.
have[B [hB hBound]]:=@current_flat_uniform_test_bound R h2 (1+1)%N 0%N AB hAB TT 2 hFlat
  (ltac:(by rewrite ler0n)).
have[M [_ hStrict]]:=@harmonic_partial_sums_unbounded R B.
have hUpper:=hBound (psi M) (fun z hz=>
  conj (le_trans (@weighted_interval_product_test_point_bounds R h2 M z hz).1
    (ltac:(by rewrite ler1n):((1:R)<=2)))
    (@weighted_interval_product_test_point_bounds R h2 M z hz).2).
rewrite weighted_interval_product_test_action in hUpper.
have hReal:=le_trans (ler_norm (harmonic_partial_sum R M)) hUpper.
by have:=le_lt_trans hReal hStrict;rewrite ltxx.
Qed.

(** Source for [weighted_interval_mixed_product_not_flat]:
    the actual original S times T
    does not belong to F_1(R^2),
    since boundary(S times T)=T times T,
    exactly the final conclusion of
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_mixed_product_not_flat:
  ~@is_flat_current R h2 (1+1)%N 1%N AB hAB ST.
Proof.
move=>[K hFlat].
have hBoundary:=@current_cartesian_boundary_first_zero R h2 1%N 1%N Full Full hFull hFull 0%N S T.
rewrite current_degree_transport_identity in hBoundary.
apply:weighted_interval_boundary_square_not_flat;exists K.
have h:=@flat_current_boundary_supported R h2 (1+1)%N 0%N AB hAB K ST hFlat.
by rewrite hBoundary in h.
Qed.
End WeightedIntervalProductNotFlat.
