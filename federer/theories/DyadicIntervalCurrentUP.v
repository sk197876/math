(** Federer (1969), 4.1.12, p. 368: the
    original sum of [2^(-2k),2^(1-2k)], k>=1.
    Specify its value by convergence of the actual
    finite segment-current prefixes on every original test.
    Flatness, mass and support are later conclusions,
    rather than requirements hidden in the definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces
  OrientedSegmentCurrentSealed ScalarSegmentCoordinateValues DyadicCurrentEndpointArithmetic CurrentWeakSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section DyadicIntervalCurrentUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation C := (@current_space R h2 1%N Full hFull 1%N).

(** Source for [dyadic_interval_current_term]: the
    actual kth original oriented interval, with formal
    index n denoting printed k=n+1, in Federer
    4.1.12, p. 368. It aliases the existing
    sealed segment current, without choosing a new one. *)
Definition dyadic_interval_current_term k:C:=
  @OrientedSegmentCurrent.value R h2 1%N Full hFull
    (euclidean_one_embed (dyadic_current_left_endpoint R k))
    (euclidean_one_embed (dyadic_current_right_endpoint R k))
    (@scalar_segment_full_domain R (dyadic_current_left_endpoint R k) (dyadic_current_right_endpoint R k)).

(** Source for [dyadic_interval_current_prefix]: the
    literal first n original intervals, supporting the
    current series in Federer 4.1.12, p. 368. *)
Definition dyadic_interval_current_prefix k:C:=\sum_(j<k) dyadic_interval_current_term j.

(** Source for [is_dyadic_interval_current_series]:
    the independently specified meaning of the original
    series in Federer 4.1.12, p. 368:
    every original test sees the limit of its
    actual finite-prefix values. Existence is separate. *)
Definition is_dyadic_interval_current_series (S:C):Prop:=
  @is_current_weak_sequence_limit R h2 1%N 1%N Full hFull dyadic_interval_current_prefix S.

(** Source for [dyadic_interval_current_series_unique]: the
    independently specified original series has at most
    one current value, supporting Federer 4.1.12,
    p. 368, by the preceding test-limit uniqueness. *)
Theorem dyadic_interval_current_series_unique (S T:C):
  is_dyadic_interval_current_series S->is_dyadic_interval_current_series T->S=T.
Proof. exact:(@current_weak_sequence_limit_unique R h2 1%N 1%N Full hFull dyadic_interval_current_prefix S T). Qed.
End DyadicIntervalCurrentUP.
