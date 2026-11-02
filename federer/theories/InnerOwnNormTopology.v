(** Federer (1969), 3.2.3, pp. 243–244: the area
    proof uses Euclidean Borel sets and Hausdorff measures.
    These topology adapters identify the metric of a specified
    inner product with the metric of its abstract norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  NormMetric NormMetricScaleContinuity HomeomorphismUP ContinuousBorelPreimages TopologicalBorel
  HausdorffMeasure HausdorffIsometricBijection GrassmannAbbreviations EuclideanInnerProduct
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_own_norm_homeomorphism]: supporting
    compatibility of the Euclidean topology in Federer 3.2.3,
    p. 243. Both metric interfaces have exactly the same
    distance, so identity and its inverse are continuous. *)
Lemma inner_own_norm_homeomorphism (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B):
  is_homeomorphism_with_inverse
    (fun x:inner_metric_space hB=>(x:real_norm_metric_space (inner_norm_real_norm hB)))
    (fun x:real_norm_metric_space (inner_norm_real_norm hB)=>(x:inner_metric_space hB)).
Proof.
constructor.
- apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01).
  by move=>x y; change (is_true (inner_norm hB (x-y)<=1*inner_norm hB (x-y))); rewrite mul1r.
- apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01).
  by move=>x y; change (is_true (inner_norm hB (x-y)<=1*inner_norm hB (x-y))); rewrite mul1r.
- by move=>x.
- by move=>x.
Qed.

(** Source for [inner_own_norm_borel_iff]: the Borel
    sets in Federer 3.2.3, p. 243, are independent
    of which of these identical metric interfaces is used. *)
Lemma inner_own_norm_borel_iff (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) (A:set X):
  @borel_set [the topologicalType of inner_metric_space hB] A <->
  @borel_set [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] A.
Proof.
split=>hA.
- exact (continuous_borel_preimage (homeomorphism_inverse_continuous (inner_own_norm_homeomorphism hB)) hA).
- exact (continuous_borel_preimage (homeomorphism_continuous (inner_own_norm_homeomorphism hB)) hA).
Qed.

(** Source for [inner_own_norm_hausdorff]: supporting exact
    compatibility of the Hausdorff measure used in Federer
    3.2.3, p. 243. Identity is a bijective isometry,
    so every natural-degree measure agrees on every subset. *)
Theorem inner_own_norm_hausdorff (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) k (A:set X):
  @hausdorff_measure R (real_norm_metric_space (inner_norm_real_norm hB)) k A=
    @hausdorff_measure R (inner_metric_space hB) k A.
Proof.
have hh:=@hausdorff_bijective_isometry_invariance R (inner_metric_space hB)
  (real_norm_metric_space (inner_norm_real_norm hB)) (fun x=>x) (fun x=>x)
  (fun x=>erefl x) (fun x=>erefl x) (fun x y=>erefl (inner_norm hB (x-y))) k A.
by rewrite image_id in hh.
Qed.

(** Source for [euclidean_norm_hausdorff_lebesgue]: the
    equality H^m=L^m used in Federer 3.2.3, p. 243,
    transferred to the abstract norm metric of the derivative
    and Borel cover, without a new measure definition. *)
Lemma euclidean_norm_hausdorff_lebesgue (R:realType) m (A:set (R_n R m)):
  @hausdorff_measure R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))) m A=
    euclidean_lebesgue_measure m A.
Proof.
rewrite inner_own_norm_hausdorff.
exact (euclidean_hausdorff_spherical_lebesgue A).1.
Qed.
