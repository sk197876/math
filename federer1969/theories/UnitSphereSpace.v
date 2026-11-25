(** Federer (1969), 3.2.13, pp. 250–251: the unit
    sphere as a compact Hausdorff space carrying its Hausdorff measure.
    The sphere is specified by the unit-norm equation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal functions topology subtype_topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology InnerBoundedness InnerFiniteCompactness EuclideanCoordinateMetric ConstrainedUnitSphere
  SubtypeCompactHausdorff OpenSubspaceMeasure HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP BorelRegularMeasureUP SphereGammaMass EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_unit_sphere_set]: S^(m-1) is the
    locus |u|= 1, Federer 3.2.13, p. 250. *)
Definition euclidean_unit_sphere_set (R:realType) m:
    set (inner_metric_space (@euclidean_inner_productP R m)):=
  [set u|inner_norm (@euclidean_inner_productP R m) u= 1].

(** Source for [euclidean_unit_sphere_space]: the homogeneous
    sphere in its relative topology, Federer 3.2.13, p. 251. *)
Definition euclidean_unit_sphere_space (R:realType) m:topologicalType:=
  [the topologicalType of set_type (@euclidean_unit_sphere_set R m)].

(** Source for [euclidean_unit_sphere_compact]: compactness of
    the finite-dimensional unit sphere, 1.7.1, p. 28, used
    in the homogeneous-space argument of Federer 3.2.13, p. 251. *)
Lemma euclidean_unit_sphere_compact (R:realType) m:
  compact (@euclidean_unit_sphere_set R m).
Proof.
apply:(@inner_finite_basis_boundedly_compact R (R_n R m) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) m (@coordinate_basis R m) (@coordinate_basisP R m)).
- exact:inner_unit_sphere_closed.
- exists 1=>u hu; by rewrite hu.
Qed.

(** Source for [euclidean_unit_sphere_space_compact]: the sphere
    as a compact space, Federer 3.2.13, p. 251. *)
Lemma euclidean_unit_sphere_space_compact (R:realType) m:
  compact [set:euclidean_unit_sphere_space R m].
Proof. exact (@set_type_compact_whole
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_unit_sphere_set R m) (@euclidean_unit_sphere_compact R m)). Qed.

(** Source for [euclidean_unit_sphere_space_hausdorff]: Hausdorff
    topology of the sphere as a Euclidean subspace, supporting
    Federer 3.2.13, p. 251. *)
Lemma euclidean_unit_sphere_space_hausdorff (R:realType) m:
  hausdorff_space (euclidean_unit_sphere_space R m).
Proof. apply:set_type_hausdorff; exact:(@metric_hausdorff R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]). Qed.

(** Source for [euclidean_unit_sphere_point]: a point C on
    the positive-dimensional unit sphere, chosen as a coordinate
    basis vector for the existence proof, Federer 3.2.13, p. 251. *)
Definition euclidean_unit_sphere_point (R:realType) m (hm:(0<m)%N):
    euclidean_unit_sphere_space R m:=
  exist _ (@coordinate_basis R m (Ordinal hm))
    (mem_set (@euclidean_coordinate_unit_norm R m (Ordinal hm))).

(** Source for [unit_sphere_hausdorff_measure]: Hausdorff measure
    regarded as a measure over the unit sphere itself, Federer
    3.2.13, p. 251. The existing subspace interface applies to
    arbitrary subsets despite its historical open-subspace name. *)
Definition unit_sphere_hausdorff_measure (R:realType) m:
    set (euclidean_unit_sphere_space R m)->\bar R:=
  open_subspace_measure (S:=@euclidean_unit_sphere_set R m)
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)).

(** Source for [unit_sphere_hausdorff_is_measure]: the measure
    laws on the sphere, 2.1.2, p. 54, as used
    in Federer 3.2.13, p. 251. *)
Lemma unit_sphere_hausdorff_is_measure (R:realType) m:
  is_measure (@unit_sphere_hausdorff_measure R m).
Proof. apply:open_subspace_measure_is_measure; exact:hausdorff_measure_is_measure. Qed.

(** Source for [unit_sphere_hausdorff_borel_regular]: Borel
    regularity of the sphere's Hausdorff measure, used in the
    invariant integral of Federer 3.2.13, p. 251. *)
Lemma unit_sphere_hausdorff_borel_regular (R:realType) m:
  is_borel_regular_measure (@unit_sphere_hausdorff_measure R m).
Proof.
apply:open_subspace_borel_regular; first exact:hausdorff_measure_is_measure.
exact:hausdorff_measure_borel_regular.
Qed.

(** Source for [unit_sphere_hausdorff_total]: the Gamma sphere
    mass in its intrinsic measure, Federer 3.2.13, p. 251. *)
Lemma unit_sphere_hausdorff_total (R:realType) m (hm:(0<m)%N):
  @unit_sphere_hausdorff_measure R m setT=
    (2*(euler_gamma_half R)^+m/euler_gamma (@positive_dimension_half R m hm))%:E.
Proof.
rewrite /unit_sphere_hausdorff_measure /open_subspace_measure.
have hImage:(set_val @` [set:euclidean_unit_sphere_space R m])=@euclidean_unit_sphere_set R m.
  apply/seteqP; split=>u.
  - move=>[v _ <-]; exact:set_valP.
  - move=>hu; exists (exist _ u (mem_set hu)); by [].
rewrite hImage; exact:hausdorff_unit_sphere_gamma_mass hm.
Qed.
