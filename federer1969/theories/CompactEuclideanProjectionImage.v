(** Federer (1969), 3.2.36, p. 272:
    an actual projected nonempty compact body
    belongs to the existing compact Hausdorff carrier. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace CompactSetDistanceProfile CompactHausdorffMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_euclidean_projection_image_exists]:
    supporting joint continuity of projected
    volumes in Federer 3.2.36, p. 272.
    The exact image law has a local
    nonempty compact witness in the existing
    Hausdorff carrier. No new global image
    operator is selected. All projection
    dimensions, including the zero block, remain. *)
Lemma compact_euclidean_projection_image_exists (R:realType) n m
    (p:euclidean_projection_space R n m)
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))):
  exists B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)),
    val B=euclidean_projection_linear p @` val A.
Proof.
have hCompact:=@euclidean_projected_compact_image R n m p (val A) (set_valP A).1.
have hNonempty:euclidean_projection_linear p @` val A!=set0.
  have [a ha]:=(set_valP A).2; exists (euclidean_projection_linear p a); by exists a.
exists (exist _ (euclidean_projection_linear p @` val A) (mem_set (conj hCompact hNonempty))).
reflexivity.
Qed.
