(** Federer (1969), 2.5.14, p. 108: applying the Radon case of 2.5.10, p.
    101, to obtain scalar component densities without a lattice unit series.
    The corrected positive-cone extension from 2.5.9, p. 100, uses the
    actual Radon compact density proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RadonMeasureUP RadonFiniteDecomposition FiniteMeasureDecompositionUP
  FiniteDecompositionRepresentation CompactSupportFunctionUP CompactSupportFunctionLattice
  FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP DaniellIntegralUP
  RealIntegralFunctionalUP RealLatticeDensityUP RegularLatticeLoneDensity
  TotalScalarLpUP TotalScalarLpFiniteSeminorm ScalarLipschitzExtensionUP FunctionSeminormDistance
  DominatedLoneExtensionUP DenseLoneExtension RadonCompactLoneDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_dominated_compact_density]: scalar density
    needed for the Radon modification of Federer 2.5.12 in
    2.5.14, p. 108. The representative is measurable and
    bounded by one everywhere, with the actual finite integral
    formula on K(X)+. Countably measurable support is not claimed. *)
Theorem radon_dominated_compact_density (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (F A : (X -> R) -> R) :
  is_monotone_daniell_integral (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  is_daniell_integral (positive_function_lattice (@compactly_supported_continuous_functions R X)) A ->
  (forall f, positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    `|A f|<=F (fun x => `|f x|)) ->
  exists k : X -> R,
    is_real_lattice_density mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) A k /\
    forall x, `|k x|<= 1.
Proof.
move=> hF hrep hA hb.
pose C := @compactly_supported_continuous_functions R X.
pose L := positive_function_lattice C.
have hL := positive_function_lattice_laws (@compactly_supported_continuous_functions_lattice R X).
have hL0 : L (fun _ => 0).
  split; first exact: compactly_supported_zero_function.
  by move=> x.
have hd : is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)).
  move=> f hf e he.
  have [g [hg hdg]] := @radon_positive_compact_lone_dense R X mu hm hr F hrep f hf e he.
  exists g; split=> //; by split=> //; exact: hg.2.
pose S := @dense_lone_extension R X L hL F A mu hm hF hrep hL0 hd hA hb.
have [hlin [hagree hbound]] := @dense_lone_extension_specification R X L hL F A mu hm hF hrep hL0 hd hA hb.
have [G [hcompact hG]] := radon_measure_finite_decomposition hm hr.
have hSb f : total_scalar_lp mu 1 f -> `|S f|<= 1*finite_total_scalar_lp_norm mu 1 f.
  by move=> hf; rewrite mul1r; exact: hbound f hf.
have [k [hk hkbound]] := @bounded_lone_density_from_finite_decomposition R X [the choiceType of set X]
  mu hm G (fun K => K) S 1 hG (@ler01 R) hlin hSb.
exists k; split=> //; split; first exact: hk.1.
move=> f hf; have hfl := @represented_lattice_in_total_lone R X mu hm L F hrep f hf.
have hi := hk.2 f hfl; by rewrite /S (hagree f hf) in hi.
Qed.
