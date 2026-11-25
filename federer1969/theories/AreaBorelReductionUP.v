(** Federer (1969), 3.2.3, p. 243: after
    discarding null sources and critical images it suffices
    to integrate on a Borel subset of the injective
    differentiability locus. State the exact reduction laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  TopologicalBorel InjectiveDifferentialPieceUP JacobianDensityMeasure HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_borel_injective_area_subset]: the
    Borel differentiability and critical-set reductions of
    Federer 3.2.3, pp. 243–244, summarized by their
    laws. The discarded subset has zero Jacobian mass
    and null image; it need not be Lebesgue null after
    the critical points have also been discarded. *)
Definition is_borel_injective_area_subset (R:realType) m n
    (f:R_n R m->R_n R n) (A C:set (R_n R m)):Prop:=
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] C /\
  C `<=` A /\ C `<=` injective_differential_locus f /\
  euclidean_jacobian_measure f (A `\` C)=0 /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` (A `\` C))=0.
