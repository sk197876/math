(** Federer (1969), 4.1.12, p. 369: the
    original weighted interval sum is flat in
    its printed compact interval and has the
    exact numerical mass tails. Its literal
    boundary is flat there as well. All
    conclusions follow from the independently specified series. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassSealed SmoothCompactSet
  CurrentBoundary CurrentSupportGeometry FlatCurrentsUP FlatCurrentBoundary FlatCurrentFinite
  NonnegativeSequenceTail WeightedIntervalCurrentUP WeightedIntervalCurrentExistence WeightedIntervalCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WeightedIntervalCurrentLaws.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation K := (weighted_interval_current_compact R).
Local Notation S := (@WeightedIntervalCurrent.value R h2).
Local Notation M := (@CurrentMass.value R h2 1%N 1%N Full hFull).

(** Source for [weighted_interval_current_flat_and_tails]:
    the actual original S is flat in
    [0,sum 4k^(-3)] and retains every
    original numerical mass-tail bound, supporting
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_flat_and_tails:
  @is_flat_current_supported_in R h2 1%N 1%N Full hFull K S /\
  forall k,(M (S-@weighted_interval_current_prefix R h2 k)<=
    nonnegative_sequence_tail (fun j=>(weighted_interval_current_mass_cost R j)%:E) k)%E.
Proof.
have[Q [hQ hGood]]:=@weighted_interval_current_model_exists R h2.
have hEqual:S=Q:=@weighted_interval_current_series_unique R h2 S Q
  (@WeightedIntervalCurrent.laws R h2) hQ.
by rewrite hEqual.
Qed.

(** Source for [weighted_interval_current_support]: the
    actual original S has support in
    [0,sum 4k^(-3)], precisely the
    printed compact support bound in
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_support:
  @current_support R h2 1%N Full hFull 1%N S `<=` smooth_compact_carrier K.
Proof.
exact:(@flat_current_supported_support R h2 1%N 1%N Full hFull K S
  weighted_interval_current_flat_and_tails.1).
Qed.

(** Source for [weighted_interval_boundary]: the
    literal original T=boundary S, Federer
    4.1.12, p. 369. *)
Definition weighted_interval_boundary:=@current_boundary R h2 1%N 0%N Full hFull S.

(** Source for [weighted_interval_boundary_flat]: both
    S and its literal boundary T
    are flat in the original compact,
    as asserted in Federer 4.1.12,
    p. 369. *)
Theorem weighted_interval_boundary_flat:
  @is_flat_current_supported_in R h2 1%N 0%N Full hFull K weighted_interval_boundary.
Proof.
exact:(@flat_current_boundary_supported R h2 1%N 0%N Full hFull K S
  weighted_interval_current_flat_and_tails.1).
Qed.

(** Source for [weighted_interval_current_is_flat]: the
    actual original S belongs to F_1(R),
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_is_flat:@is_flat_current R h2 1%N 1%N Full hFull S.
Proof. exists K;exact:weighted_interval_current_flat_and_tails.1. Qed.

(** Source for [weighted_interval_boundary_is_flat]: the
    actual original T belongs to F_0(R),
    Federer 4.1.12, p. 369. *)
Theorem weighted_interval_boundary_is_flat:
  @is_flat_current R h2 1%N 0%N Full hFull weighted_interval_boundary.
Proof. exists K;exact:weighted_interval_boundary_flat. Qed.
End WeightedIntervalCurrentLaws.
