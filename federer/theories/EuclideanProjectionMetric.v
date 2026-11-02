(** General topology supporting the projection-incidence Suslin argument of
    Federer (1969), 2.10.5, p. 172. Add the inherited metric to the already
    defined relative Hom topology on O*(n,m). Its compactness proves
    completeness; a countable base of the finite-dimensional Hom space gives
    hereditary separability. These are background hypotheses for 2.2.10, p.
    65, not additional measure assumptions. Source context and parameter
    topology: EuclideanProjectionSpace.v and MetricSubsetBackground.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric Hom HomInner HomCompositionDeterminant InnerSpaceCountableBase
  EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace MetricSubsetBackground
  MetricSubsetSeparability CompactCauchyLimits CountableBaseDenseSet CompleteMetricUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_projection_metric_space]: supporting
    inherited metric on O*(n,m) for Federer 2.10.5,
    p. 172. The actual members and existing relative
    topology are preserved by the subtype adapter. *)
Definition orthogonal_projection_metric_space (R : realType) (n m : nat) : metricType R :=
  [the metricType R of @metric_subset R
    (inner_metric_space (hom_inner_productP (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R m) (@coordinate_basisP R n)))
    (euclidean_orthogonal_projections R n m)].

(** Source for [orthogonal_projection_metric_openE]: supporting
    topology compatibility for the parameter space in
    Federer 2.10.5, p. 172. No replacement topology
    is chosen for the subsequent Suslin or measure arguments. *)
Lemma orthogonal_projection_metric_openE (R : realType) (n m : nat)
    (U : set (orthogonal_projection_metric_space R n m)) :
  open U <-> @open (euclidean_projection_space R n m) U.
Proof. by []. Qed.

(** Source for [orthogonal_projection_metric_complete]: supporting
    complete source for the continuous Suslin-image theorem
    used in Federer 2.10.5, p. 172. Compactness
    supplies a cluster point for each proper Cauchy filter. *)
Theorem orthogonal_projection_metric_complete (R : realType) (n m : nat) :
  is_complete_metric_space (orthogonal_projection_metric_space R n m).
Proof.
apply: compact_metric_space_complete; exact: (@euclidean_projection_space_compact R n m).
Qed.

(** Source for [orthogonal_projection_metric_separable]: supporting
    separable source for the Suslin argument in Federer
    2.10.5, p. 172. Choose a dense set existentially
    from an ambient finite-dimensional countable base,
    then use hereditary metric separability. *)
Theorem orthogonal_projection_metric_separable (R : realType) (n m : nat) :
  exists D : set (orthogonal_projection_metric_space R n m), countable D /\ dense D.
Proof.
pose hH := hom_inner_productP (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R m) (@coordinate_basisP R n).
have [U hU] := inner_space_countable_open_base hH
  (hom_rank_one_baseP (@coordinate_basisP R n) (@coordinate_basisP R m)).
have hsep := @countable_open_base_dense_set (inner_metric_space hH) 0 U hU.
exact (@metric_subset_separable R (inner_metric_space hH)
  (euclidean_orthogonal_projections R n m) hsep).
Qed.
