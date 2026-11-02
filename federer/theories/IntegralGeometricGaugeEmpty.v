(** Federer (1969), 3.2.36, p. 273: empty transported
    convex generators have their actual zero cost. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  ProjectedVolumeMeasurability IntegralGeometricGauge OrthogonalProjectionProbability
  NonnegativeExtendedProbabilityConstant EuclideanLebesgueDimensions MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_empty]: the empty cover
    slots in the isometry transport for Federer 3.2.36, p. 273.
    Every actual projection of the empty set has zero Lebesgue volume;
    the opaque probability-norm constant law then proves its normalized
    cost zero. All natural dimensions and admissible exponents remain,
    including degree zero; no nonempty-source convention is misapplied. *)
Lemma integral_geometric_gauge_empty (R:realType) n k (hkn:(k<=n)%N) t:
  1<=t ->@integral_geometric_gauge R n k hkn t set0=0.
Proof.
move=>ht.
pose P:=orthogonal_projection_metric_space R n k.
have hFunction:projected_volume_function (m:=k) set0=(fun _:P=>(0: \bar R)).
  apply:funext=>p; rewrite /projected_volume_function image_set0.
  exact:measure_empty (euclidean_lebesgue_is_measure R k).
rewrite /integral_geometric_gauge hFunction
  (@probability_nonnegative_extended_constant_norm R P
    (@orthogonal_projection_probability R n k hkn) (@theta_star_is_measure R n k hkn)
    0 t (@theta_star_total R n k hkn) (lexx 0) ht) mule0.
reflexivity.
Qed.
