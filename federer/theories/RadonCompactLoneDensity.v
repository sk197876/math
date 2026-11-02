(** Federer (1969), 2.5.14, p. 108: positive K(X) density for the Radon
    variation measure, supplying the extension step without a lattice unit
    series. The proof uses actual compact characteristic approximations and
    the finite-simple reduction of 2.5.3, p. 95. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialExtendedOrderLoci
  FunctionLatticeUP FunctionLatticeLaws CompactSupportFunctionUP CompactSupportFunctionLattice RadonMeasureUP RadonCompactCharacteristicApproximation PositiveLatticeDensityFromCharacteristics
  RealIntegralFunctionalUP SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  CharacteristicFunctionUP LatticeL1ApproximationUP RegularLatticeLoneDensity TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm TotalScalarPairing
  TotalLoneSummability TotalAbsoluteDifferenceGraph ScalarLipschitzExtensionUP FunctionSeminormDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_positive_compact_lone_dense]: supporting
    positive-cone density for the Radon vector generalization in
    Federer 2.5.14, p. 108. No K(X)-regularity or
    countability assumption is imposed on the Radon measure. *)
Theorem radon_positive_compact_lone_dense (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (F : (X -> R) -> R)
    (hF : is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F) :
  is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice (@compactly_supported_continuous_functions R X))
    (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)).
Proof.
move=> f [hf hf0] e he.
pose K := @compactly_supported_continuous_functions R X.
pose L := positive_function_lattice K.
have hL := positive_function_lattice_laws (@compactly_supported_continuous_functions_lattice R X).
have hs := @total_lone_summable_real R X mu hm f hf.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: hf0.
have hzero : L (fun _ => 0%R).
  split; first exact: compactly_supported_zero_function.
  by move=> x.
have hchar S v : is_characteristic_function S v -> measure_measurable mu S -> mu S < +oo ->
    is_positive_lattice_l1_approximable mu L v.
  move=> hv hS hfin.
  have [hs' ha] := @radon_compact_characteristic_approximable R X mu hm hr F hF S v hv hS hfin.
  split=> // d hd.
  have [u [a [hu [hi' he']]]]:=ha d hd.
  exists u,a; split; last by split.
  by split=> //; exact: hu.2.
have [h [q [hh [hi hqe]]]] := @positive_lattice_density_from_characteristics R X L F hL mu hm hF
  hzero hchar
  (real_total_integrand f) e hs hp he.
have hmem := @represented_lattice_in_total_lone R X mu hm L F hF h hh.1.
have hd := @total_scalar_lp_subtract R X mu hm 1 h f hmem hf.
have hqi : is_measure_integral mu (real_total_integrand (fun x => `|h x-f x|%R)) q%:E.
  exact: (@measure_integral_graph_equivalent R X mu _ _ _ (total_absolute_difference_graph h f) hi).
have hNi := @total_scalar_lone_absolute_integral R X mu hm _ hd.
have hNq : finite_total_scalar_lp_norm mu 1 (fun x => (h x-f x)%R)=q.
  exact: EFin_inj (measure_integral_unique hNi hqi).
exists h; split; first exact: hh.1.
have hsymmetric := (function_seminorm_distance_laws
  (@total_scalar_lp_vector_lattice R X mu hm 1 (lexx _))
  (@finite_total_scalar_lp_norm_laws R X mu hm 1)).2.2.1 f h hf hmem.
rewrite hsymmetric /function_seminorm_distance hNq; exact: hqe.
Qed.
