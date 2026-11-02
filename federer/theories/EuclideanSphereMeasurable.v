(** Federer (1969), 3.2.13, p. 250: sphere
    restrictions in the polar integrals are measurable.
    Their closedness is a norm-topology fact; no
    finite Hausdorff mass is assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerNormedTopology
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_norm_sphere_closed]: the closed
    radius-r spheres in the polar decomposition,
    Federer 3.2.13, p. 250. The
    supporting statement includes negative radii, where
    the sphere is empty, and source dimension zero. *)
Lemma euclidean_norm_sphere_closed (R:realType) m (r:R):
  closed [set x:inner_metric_space (@euclidean_inner_productP R m) |
    inner_norm (@euclidean_inner_productP R m) x=r].
Proof.
change (closed ((fun x:inner_metric_space (@euclidean_inner_productP R m)=> (`|x| : R^o)) @^-1` [set r])).
apply:preimage_closed; first by move=>x _; exact:norm_continuous.
apply:compact_closed; [exact:norm_hausdorff|exact:compact_set1].
Qed.

(** Source for [euclidean_norm_sphere_hausdorff_measurable]:
    measurable sphere restrictions needed in the
    two polar integrals of Federer 3.2.13,
    p. 250, for every natural Hausdorff degree. *)
Lemma euclidean_norm_sphere_hausdorff_measurable (R:realType) m k (r:R):
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k)
    [set x|inner_norm (@euclidean_inner_productP R m) x=r].
Proof.
apply:(@borel_regular_borel_measurable R (inner_metric_space (@euclidean_inner_productP R m)) _
  (@hausdorff_measure_is_measure R _ k) (@hausdorff_measure_borel_regular R _ k)).
exact (closed_borel_set (@euclidean_norm_sphere_closed R m r)).
Qed.
