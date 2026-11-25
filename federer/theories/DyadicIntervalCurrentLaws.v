(** Federer (1969), 4.1.12, p. 368: the
    original interval sum is flat in the
    common interval [0,1/2]. Derive this and
    its quantitative mass tails from the opaque
    original testwise series law and uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassSealed FlatCurrentsUP
  ScalarCurrentIntervalCompact DyadicCurrentEndpointArithmetic DyadicIntervalCurrentUP
  DyadicIntervalCurrentExistence DyadicIntervalCurrentSealed CurrentBoundary FlatCurrentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DyadicIntervalCurrentLaws.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation K := (scalar_current_compact_interval R 0 (1/2)).
Local Notation S := (@DyadicIntervalCurrent.value R h2).
Local Notation M := (@CurrentMass.value R h2 1%N 1%N Full hFull).

(** Source for [dyadic_interval_current_flat_and_tails]:
    the original opaque sum is flat in
    [0,1/2] and the mass after its first
    n intervals is at most (1/4)^n/3,
    supporting Federer 4.1.12, p. 368. *)
Theorem dyadic_interval_current_flat_and_tails:
  @is_flat_current_supported_in R h2 1%N 1%N Full hFull K S /\
  forall k,(M (S-@dyadic_interval_current_prefix R h2 k)<=
    (dyadic_current_mass_tail R k)%:E)%E.
Proof.
have[Q [hQ hGood]]:=@dyadic_interval_current_model_exists R h2.
have hEqual:S=Q:=@dyadic_interval_current_series_unique R h2 S Q
  (@DyadicIntervalCurrent.laws R h2) hQ.
by rewrite hEqual.
Qed.

(** Source for [dyadic_interval_boundary]: the
    literal boundary of the original interval
    sum in Federer 4.1.12, p. 368.
    This aliases the existing boundary operator. *)
Definition dyadic_interval_boundary:=@current_boundary R h2 1%N 0%N Full hFull S.

(** Source for [dyadic_interval_boundary_flat]: the
    original boundary T is flat in the
    common interval [0,1/2], as asserted in
    Federer 4.1.12, p. 368. *)
Theorem dyadic_interval_boundary_flat:
  @is_flat_current_supported_in R h2 1%N 0%N Full hFull K dyadic_interval_boundary.
Proof.
exact:(@flat_current_boundary_supported R h2 1%N 0%N Full hFull K S
  dyadic_interval_current_flat_and_tails.1).
Qed.
End DyadicIntervalCurrentLaws.
