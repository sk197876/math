(** Federer (1969), 4.1.12, p. 369: the
    original S=sum_[k>=1] k[u_k,v_k].
    Specify its value only by the
    original testwise limits of its literal
    weighted finite prefixes. Flatness, support
    and mass are later proved conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces SmoothCompactSet
  OrientedSegmentCurrentSealed ScalarSegmentCoordinateValues ScalarCurrentIntervalCompact
  ReciprocalPowerSeriesBounds WeightedIntervalEndpoints CurrentWeakSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [weighted_interval_current_compact]: the
    exact original compact support interval
    [0,sum_[k>=1] 4k^(-3)] in
    Federer 4.1.12, p. 369.
    The numerical sum is already proved finite. *)
Definition weighted_interval_current_compact (R:realType):
    smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R 1%N))
      (fun _:R_n R 1%N=>True):=
  scalar_current_compact_interval R 0 (weighted_interval_support_endpoint R).

(** Source for [weighted_interval_current_mass_cost]: the
    exact original kth mass coefficient
    2k^(-2), supporting the displayed total
    mass in Federer 4.1.12, p. 369. *)
Definition weighted_interval_current_mass_cost (R:realType) n:R:=
  2*reciprocal_power_series_weight R 2%N n.

Section WeightedIntervalCurrentUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation C := (@current_space R h2 1%N Full hFull 1%N).

(** Source for [weighted_interval_current_term]: the
    literal original k[u_k,v_k], with
    formal n denoting k=n+1, in
    Federer 4.1.12, p. 369. *)
Definition weighted_interval_current_term n:C:=
  (n.+1)%:R*:@OrientedSegmentCurrent.value R h2 1%N Full hFull
    (euclidean_one_embed (weighted_interval_left_endpoint R n))
    (euclidean_one_embed (weighted_interval_right_endpoint R n))
    (@scalar_segment_full_domain R (weighted_interval_left_endpoint R n) (weighted_interval_right_endpoint R n)).

(** Source for [weighted_interval_current_prefix]: the
    first N original weighted segments,
    supporting Federer 4.1.12, p. 369. *)
Definition weighted_interval_current_prefix N:C:=\sum_(j<N) weighted_interval_current_term j.

(** Source for [is_weighted_interval_current_series]:
    the independently stated original testwise
    series law for S in Federer
    4.1.12, p. 369. No
    mass or flatness property is assumed. *)
Definition is_weighted_interval_current_series (S:C):Prop:=
  @is_current_weak_sequence_limit R h2 1%N 1%N Full hFull weighted_interval_current_prefix S.

(** Source for [weighted_interval_current_series_unique]:
    the original series specification determines
    at most one actual current,
    supporting Federer 4.1.12, p. 369. *)
Theorem weighted_interval_current_series_unique (S T:C):
  is_weighted_interval_current_series S->is_weighted_interval_current_series T->S=T.
Proof. exact:(@current_weak_sequence_limit_unique R h2 1%N 1%N Full hFull weighted_interval_current_prefix S T). Qed.
End WeightedIntervalCurrentUP.
