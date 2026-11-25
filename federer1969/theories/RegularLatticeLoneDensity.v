(** Federer (1969), 2.5.9, p. 100: positive-lattice density in total L1+, as
    corrected in erratum p. 2, book p. 100 lines 21–24, especially line 22.
    The density theorem itself was proved for 2.5.3, p. 94. This module
    expresses that actual result in the abstract extension's distance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialExtendedOrderLoci
  FunctionLatticeUP FunctionLatticeRegularityUP RegularDaniellEnvelope DaniellPositiveL1Density
  RealIntegralFunctionalUP SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm TotalScalarPairing
  TotalLoneSummability TotalAbsoluteDifferenceGraph ScalarLipschitzExtensionUP FunctionSeminormDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_in_total_lone]: inclusion L in total L1
    used in Federer 2.5.9, p. 100 *)
Lemma represented_lattice_in_total_lone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (F : (X -> R) -> R) :
  is_real_integral_functional mu L F -> forall f, L f -> total_scalar_lp mu 1 f.
Proof.
move=> hF f hf; apply: (@summable_real_total_lone R X mu hm f).
exists (F f); exact: hF f hf.
Qed.

(** Source for [regular_positive_lattice_lone_dense]: the exact
    positive-density step of Federer 2.5.9, p. 100, after erratum p. 2 line
    22 Density is proved from the regular representing measure and is not
    assumed as a functional-extension axiom. *)
Theorem regular_positive_lattice_lone_dense (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_real_integral_functional mu L F -> is_function_lattice_regular L mu ->
  is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)).
Proof.
move=> hF hr f [hf hf0] e he.
have hs := @total_lone_summable_real R X mu hm f hf.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: hf0.
have hc := @regular_representing_measure_envelope R X L F hL mu hm hF hr.
have [h [q [hh [hi hqe]]]] := @daniell_nonnegative_summable_lattice_density R X L F hL mu hm hF hc
  (real_total_integrand f) e hs hp he.
have hmem := @represented_lattice_in_total_lone R X mu hm L F hF h hh.1.
have hd := @total_scalar_lp_subtract R X mu hm 1 h f hmem hf.
have hqi : is_measure_integral mu (real_total_integrand (fun x => `|h x-f x|%R)) q%:E.
  exact: (@measure_integral_graph_equivalent R X mu _ _ _ (total_absolute_difference_graph h f) hi).
have hNi := @total_scalar_lone_absolute_integral R X mu hm _ hd.
have hNq : finite_total_scalar_lp_norm mu 1 (fun x => (h x-f x)%R)=q.
  exact: EFin_inj (measure_integral_unique hNi hqi).
exists h; split=> //.
have hsymmetric := (function_seminorm_distance_laws
  (@total_scalar_lp_vector_lattice R X mu hm 1 (lexx _))
  (@finite_total_scalar_lp_norm_laws R X mu hm 1)).2.2.1 f h hf hmem.
rewrite hsymmetric /function_seminorm_distance hNq; exact: hqe.
Qed.
