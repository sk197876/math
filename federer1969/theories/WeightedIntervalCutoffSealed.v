(** Federer (1969), 4.1.12, p. 369:
    seal the proved original phi_k family.
    Only the independent support, range,
    unit value and derivative laws are public. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces WeightedIntervalCutoffUP WeightedIntervalCutoffExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type WeightedIntervalCutoffSignature.
(** Source for [value]: the original actual
    scalar test family phi_k of
    Federer 4.1.12, p. 369. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0),nat->
  @current_test_space R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 0%N.
(** Source for [laws]: all independent original
    phi_k laws, Federer 4.1.12, p. 369. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0),
  @is_weighted_interval_cutoff_family R h2 (@value R h2).
End WeightedIntervalCutoffSignature.
Module WeightedIntervalCutoff:WeightedIntervalCutoffSignature.
(** Source for [value]: the proved witness
    stays behind the opaque interface,
    supporting Federer 4.1.12, p. 369. *)
Definition value (R:realType) (h2:(1+1:R)!=0):=
  projT1 (cid (@weighted_interval_cutoff_family_exists R h2)).
(** Source for [laws]: the hidden family
    satisfies the original laws by its
    proved existence, Federer 4.1.12, p. 369. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0):@is_weighted_interval_cutoff_family R h2 (@value R h2).
Proof. exact:projT2 (cid (@weighted_interval_cutoff_family_exists R h2)). Qed.
End WeightedIntervalCutoff.
