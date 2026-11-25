(** Federer (1969), 4.1.12, p. 368: the
    original dyadic interval series stays opaque after
    its independently stated testwise limit is proved
    to exist and to be unique. Flatness and
    mass bounds are consumers of this original law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces DyadicIntervalCurrentUP DyadicIntervalCurrentExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type DyadicIntervalCurrentSignature.
(** Source for [value]: the original sum of
    [2^(-2k),2^(1-2k)] for k>=1 in Federer
    4.1.12, p. 368, specified independently
    by the original finite-prefix test limits. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0),
  @current_space R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 1%N.
(** Source for [laws]: the opaque current has
    exactly the original testwise interval-series law,
    supporting Federer 4.1.12, p. 368. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0),
  @is_dyadic_interval_current_series R h2 (@value R h2).
End DyadicIntervalCurrentSignature.

Module DyadicIntervalCurrent:DyadicIntervalCurrentSignature.
(** Source for [value]: a proved existence witness
    realizes the independently specified original series
    of Federer 4.1.12, p. 368. Its
    implementation is hidden by the signature. *)
Definition value (R:realType) (h2:(1+1:R)!=0):=
  projT1 (cid (@dyadic_interval_current_series_exists R h2)).
(** Source for [laws]: the selected witness has
    the original series law by its proved
    existence, supporting Federer 4.1.12, p. 368. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0):
  @is_dyadic_interval_current_series R h2 (@value R h2).
Proof. exact:projT2 (cid (@dyadic_interval_current_series_exists R h2)). Qed.
End DyadicIntervalCurrent.
