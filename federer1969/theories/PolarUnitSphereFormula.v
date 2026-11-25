(** Federer (1969), 3.2.13, p. 250: the
    second displayed polar integration equality. Positive
    sphere dilation preserves exact inner domains;
    the outer integral follows by graph equivalence. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLebesgueDimensions LebesgueScalarMeasure
  PolarSphereFormula RadialSphereIntegral PolarUnitSphereIntegral PartialFunctionUP PartialZeroExtension
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [polar_unit_sphere_integral_formula]: the
    second displayed formula in Federer 3.2.13,
    p. 250: integrate g(r u) over
    the unit sphere and then r^(m-1)
    over positive radii. All positive source
    dimensions, signed infinite values and exact
    partial inner-integrability domains are retained. *)
Theorem polar_unit_sphere_integral_formula (R:realType) m (g:R_n R m->R):
  (0<m)%N ->is_measure_integrable (@euclidean_lebesgue_measure R m) (real_total_integrand g) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m) (real_total_integrand g) a /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
      (weighted_unit_sphere_integral (real_total_integrand g)) a.
Proof.
move=>hm hg; have [a [hI hSphere]]:=polar_sphere_integral_formula hm hg.
exists a; split=>//.
apply:measure_integral_graph_equivalent _ hSphere=>r z.
rewrite !partial_function_zero_extension_graph.
split.
- move=>[[hr hz]|[hr hz]].
  + left; split=>//; exact ((@radial_unit_sphere_integral_graph R m (real_total_integrand g) r z hr).1 hz).
  + right; by split.
- move=>[[hr hz]|[hr hz]].
  + left; split=>//; exact ((@radial_unit_sphere_integral_graph R m (real_total_integrand g) r z hr).2 hz).
  + right; by split.
Qed.
