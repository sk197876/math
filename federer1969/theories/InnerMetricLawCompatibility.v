(** Federer (1969), 1.7.1, p. 28, supporting the suitable
    Euclidean ambient spaces of 3.2.28, pp. 263–267:
    the norm, topology and Hausdorff measure depend on the
    stated inner product, independently of a proof of its laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric NormMetricScaleContinuity
  HomeomorphismUP HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_norm_law_compatibility]: uniqueness of
    the nonnegative square root in 1.7.1, p. 28,
    as used for the metric identifications of 3.2.28,
    pp. 263–267. Only the public norm laws are used. *)
Lemma inner_norm_law_compatibility (R:realType) (V:lmodType R)
    (B:V->V->R) (hB hC:is_inner_product B) x:
  inner_norm hB x=inner_norm hC x.
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
exact:inner_norm_sqr.
Qed.

(** Source for [inner_metric_law_homeomorphism]: the
    identical metrics specified by 1.7.1, p. 28,
    supporting the ambient spaces of 3.2.28, pp. 263–267. *)
Lemma inner_metric_law_homeomorphism (R:realType) (V:lmodType R)
    (B:V->V->R) (hB hC:is_inner_product B):
  is_homeomorphism_with_inverse
    (fun x:inner_metric_space hB=>(x:inner_metric_space hC))
    (fun x:inner_metric_space hC=>(x:inner_metric_space hB)).
Proof.
constructor; last first.
- by move=>x.
- by move=>x.
- apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01).
  move=>x y; rewrite !inner_metric_distanceE mul1r.
  by rewrite (inner_norm_law_compatibility hB hC).
- apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01).
  move=>x y; rewrite !inner_metric_distanceE mul1r.
  by rewrite (inner_norm_law_compatibility hB hC).
Qed.

(** Source for [inner_metric_law_hausdorff]: Hausdorff measure
    depends only on the prescribed metric, 2.10.2, p. 171,
    supporting the fibre measures in 3.2.28, pp. 265–267. *)
Theorem inner_metric_law_hausdorff (R:realType) (V:lmodType R)
    (B:V->V->R) (hB hC:is_inner_product B) k (A:set V):
  @hausdorff_measure R (inner_metric_space hB) k A=
  @hausdorff_measure R (inner_metric_space hC) k A.
Proof.
have h:=@hausdorff_bijective_isometry_invariance R (inner_metric_space hC)
  (inner_metric_space hB) (fun x=>x) (fun x=>x)
  (fun x=>erefl x) (fun x=>erefl x)
  (fun x y=>inner_norm_law_compatibility hB hC (x-y)) k A.
by rewrite image_id in h.
Qed.
