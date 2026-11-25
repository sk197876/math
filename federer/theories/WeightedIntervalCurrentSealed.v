(** Federer (1969), 4.1.12, p. 369:
    the original weighted interval series
    stays opaque after its independent
    testwise value is proved to exist
    and to be unique. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces WeightedIntervalCurrentUP WeightedIntervalCurrentExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type WeightedIntervalCurrentSignature.
(** Source for [value]: the actual original
    sum k[u_k,v_k] in Federer
    4.1.12, p. 369. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0),
  @current_space R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 1%N.
(** Source for [laws]: exactly the independent
    original weak-series specification, supporting
    Federer 4.1.12, p. 369. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0),
  @is_weighted_interval_current_series R h2 (@value R h2).
End WeightedIntervalCurrentSignature.
Module WeightedIntervalCurrent:WeightedIntervalCurrentSignature.
(** Source for [value]: select the proved
    original series witness behind the
    opaque interface, Federer 4.1.12, p. 369. *)
Definition value (R:realType) (h2:(1+1:R)!=0):=
  projT1 (cid (@weighted_interval_current_series_exists R h2)).
(** Source for [laws]: the hidden current
    has the independent series law,
    supporting Federer 4.1.12, p. 369. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0):@is_weighted_interval_current_series R h2 (@value R h2).
Proof. exact:projT2 (cid (@weighted_interval_current_series_exists R h2)). Qed.
End WeightedIntervalCurrent.
