(** Federer (1969), 3.3.4, pp. 290–291: the
    actual compact projective image with its inherited
    symmetric Hilbert metric. Its orthogonal action
    and unit-sphere parametrization use only the
    existing symmetric-power laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  SymmetricGrading InnerSymmetricPositivity SymmetricSquareGeometry
  StructureProjectiveSphere StructureProjectiveRotation StructureProjectiveTransport
  UnitSphereSpace UnitSphereOrthogonalAction MetricSubsetBackground
  CompactMetricSubset EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_space]: the
    actual metric subspace T(U) of the second
    symmetric Hilbert power in Federer 3.3.4,
    p. 290. No quotient representative is selected. *)
Definition structure_projective_space (R:realType) m:metricType R:=
  [the metricType R of metric_subset (@structure_projective_sphere R m)].

(** Source for [structure_projective_quotient]: the
    actual map T restricted to the unit sphere,
    Federer 3.3.4, p. 290, with its actual
    projective image as codomain. *)
Definition structure_projective_quotient (R:realType) m
    (u:metric_subset (@euclidean_unit_sphere_set R m.+1)):
    structure_projective_space R m:=
  Sub (inner_projective_square (val u))
    (mem_set (ex_intro2 (fun x=>@euclidean_unit_sphere_set R m.+1 x)
      (fun x=>inner_projective_square x=inner_projective_square (val u))
      (val u) (set_valP u) erefl)).

(** Source for [structure_projective_action]: the
    actual orthogonal action on the original T(U),
    Federer 3.3.4, p. 290. Image preservation
    was proved before this codomain restriction. *)
Definition structure_projective_action (R:realType) m
    (g:euclidean_orthogonal_group R m.+1) (z:structure_projective_space R m):
    structure_projective_space R m:=
  Sub (structure_projective_rotation g (val z))
    (mem_set (structure_projective_rotation_member g (set_valP z))).

(** Source for [structure_projective_space_compact]:
    the actual T(U) is compact as its own
    metric space, Federer 3.3.4, p. 290. *)
Theorem structure_projective_space_compact (R:realType) m:
  compact (@setT (structure_projective_space R m)).
Proof. exact:(compact_metric_subset_whole (@structure_projective_sphere_compact R m)). Qed.

(** Source for [structure_projective_action_isometry]:
    the restricted action preserves the actual
    inherited distance on T(U), Federer 3.3.4,
    p. 290. *)
Lemma structure_projective_action_isometry (R:realType) m
    (g:euclidean_orthogonal_group R m.+1) (x y:structure_projective_space R m):
  mdist (structure_projective_action g x) (structure_projective_action g y)=mdist x y.
Proof.
rewrite !metric_subset_distanceE.
exact:(@structure_projective_rotation_isometry R m g (val x) (val y)
  (set_valP x) (set_valP y)).
Qed.
