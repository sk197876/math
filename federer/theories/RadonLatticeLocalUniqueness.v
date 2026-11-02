(** Federer (1969), 2.5.14, p. 108: the Radon representing densities are
    only locally almost unique when hypothesis (3) of 2.5.12 is removed.
    This scalar supporting theorem tests the difference against compact
    cutoffs. Positive density and dominated convergence follow the proof of
    2.5.9, p. 100. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground MeasureUP RadonMeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP FunctionLatticeUP FunctionLatticeLaws
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP CompactCutoff
  RealIntegralFunctionalUP MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic
  TotalScalarLpUP TotalScalarMeasurability TotalScalarLpFiniteSeminorm FunctionSeminormDistance
  ScalarLipschitzExtensionUP RealLatticeDensityUP DenseLatticeZeroPairing
  RadonCompactLoneDensity LocallyNullMeasureUP RadonLocallyNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_compact_lattice_density_locally_unique]:
    supporting scalar form of the local uniqueness qualification
    in Federer 2.5.14, p. 108. Competing densities need
    only be measurable and represent the same functional on K(X)+;
    no common pointwise or essential bound is imposed. *)
Theorem radon_compact_lattice_density_locally_unique (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (F A : (X -> R) -> R) (k l : X -> R) :
  is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  is_real_lattice_density mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) A k ->
  is_real_lattice_density mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) A l ->
  measure_locally_almost_everywhere mu [set x | k x=l x].
Proof.
move=> hrep hk hl.
pose C := @compactly_supported_continuous_functions R X.
pose L := positive_function_lattice C.
have hL := positive_function_lattice_laws (@compactly_supported_continuous_functions_lattice R X).
have hdense : is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)).
  move=> f hf e he.
  have [g [hg hd]] := @radon_positive_compact_lone_dense R X mu hm hr F hrep f hf e he.
  exists g; split=> //; by split=> //; exact: hg.2.
pose w x := (k x-l x)%R.
have hw : is_measure_measurable_function mu (total_scalar_function w).
  apply: (@total_scalar_continuous_binary_operation R X mu hm k l (fun p => (p.1-p.2)%R) _ hk.1 hl.1).
  change (continuous (fun p : R^o * R^o => (p.1-p.2)%R)).
  move=> p; apply: cvgB; [exact: cvg_fst|exact: cvg_snd].
have hz f : L f -> is_measure_integral mu (real_total_integrand (fun x => (f x*w x)%R)) 0.
  move=> hf.
  have hi := @real_total_integral_subtract R X mu hm
    (fun x => (f x*k x)%R) (fun x => (f x* l x)%R) (A f) (A f) (hk.2 f hf) (hl.2 f hf).
  rewrite subrr in hi.
  have he : (fun x => (f x*k x-f x* l x)%R)=(fun x => (f x*w x)%R).
    by apply: funext=> x; rewrite /w mulrBr.
  by rewrite he in hi.
apply/(radon_locally_null_compact_iff hm hr)=> K hK.
pose u := @compact_cutoff R X K (radon_hausdorff hr) (radon_locally_compact hr) hK.
have hu := @compact_cutoff_specification R X K (radon_hausdorff hr) (radon_locally_compact hr) hK.
have hu0 : function_nonnegative u by move=> x; exact: (andP (compact_cutoff_range hu x)).1.
have huL : L u by split; first exact: compact_cutoff_function hu.
have hp := @dense_lattice_zero_pairing_product_almost_zero R X L hL F mu hm w hrep hdense hw hz u (conj huL hu0).
apply: (@measure_null_subset R X mu hm _ _ _ hp)=> x [hx hneq] hzero.
apply: hneq; apply/eqP; rewrite -subr_eq0; apply/eqP.
have hux : u x= 1%R := compact_cutoff_on_set hu hx.
change ((u x*w x)%R=0%R) in hzero.
by rewrite hux mul1r in hzero.
Qed.
