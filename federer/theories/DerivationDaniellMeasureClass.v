(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext FunctionLatticeUP
  FunctionLatticeLevelFamilies FunctionLatticeRegularityUP BoundedSupportContinuous
  BoundedContinuousRegularity BoundedContinuousMeasureClass BoundedContinuousSummability
  SummableRealFunctionUP RealIntegralFunctionalUP RealIntegralFunctional MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measure_bounded_lattice_regular]: supporting
    regularity direction of the first observation in Federer
    2.9.10, p. 157. The pointed proof uses decreasing open
    approximants. The empty-space case has only the empty set and
    uses its explicit finite F2 hull; no inhabited-space hypothesis
    is added to the characterisation. *)
Lemma derivation_measure_bounded_lattice_regular (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi ->
  is_function_lattice_regular (@bounded_support_continuous_functions R X) phi.
Proof.
move=> hphi; case: (pselect (exists x : X, True))=> [[a _]|hempty].
- exact (@derivation_measure_bounded_lattice_regular_pointed R X phi a hphi).
- have hm := derivation_measure_law hphi.
  have hS (S : set X) : S=(@set0 X).
    apply/seteqP; split=> x; [move=> _; exfalso; apply: hempty; by exists x|by move=> []].
  have h0 : function_lattice_increasing_levels (@bounded_support_continuous_functions R X) set0.
    apply: function_lattice_strict_level_increasing.
    exact (@function_lattice_empty_strict_level R X _ (@bounded_support_continuous_lattice R X)
      (fun _ => 0%R) (@bounded_support_continuous_zero R X)).
  move=> S; split; last by move=> [W [_ [_ [he hfin]]]]; rewrite he.
  move=> _; exists set0; split; first by rewrite (hS S).
  split.
  + exists (fun _ : nat => (@set0 X)); split=> //; split; first by move=> n m hnm x [].
    split; first by rewrite (measure_empty hm) ltry.
    apply/seteqP; split=> x; first by move=> [].
    by move=> hx; exact: hx 0%N Logic.I.
  + rewrite (hS S) (measure_empty hm); split=> //; exact: ltry.
Qed.

(** Source for [derivation_measure_daniell_characterisation]: direct first
    observation in Federer 2.9.10, p. 157: M consists exactly of the
    L-regular representing measures of monotone Daniell integrals on bounded
    continuous functions with bounded support. Both implications are proved
    for arbitrary metric X, including the empty space, without local
    compactness. The representing functional and regularity use the existing
    abstract specifications of 2.5.1–2.5.3. *)
Theorem derivation_measure_daniell_characterisation (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi <->
    is_measure phi /\ exists lambda : (X -> R) -> R,
      is_monotone_daniell_integral (@bounded_support_continuous_functions R X) lambda /\
      is_real_integral_functional phi (@bounded_support_continuous_functions R X) lambda /\
      is_function_lattice_regular (@bounded_support_continuous_functions R X) phi.
Proof.
split.
- move=> hphi; have hm := derivation_measure_law hphi.
  have hsum := @bounded_support_continuous_summable R X phi hphi.
  split=> //; exists (@lattice_measure_integral R X phi _ hsum); split.
  + exact (@summable_sublattice_integral_laws R X phi hm _ hsum (@bounded_support_continuous_lattice R X)).
  + split; first exact: lattice_measure_integral_specification.
    exact: derivation_measure_bounded_lattice_regular hphi.
- move=> [hm [lambda [_ [hrep hreg]]]].
  exact: bounded_continuous_regular_measure_in_class hm hrep hreg.
Qed.
