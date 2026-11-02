(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureDerivationContext BorelRegularMeasureUP
  TopologicalBorel FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability
  FunctionLatticeRegularityUP RealIntegralFunctionalUP CoveringFamilyUP BoundedUnitTests
  BoundedSupportContinuous BoundedContinuousOpenLevels BoundedContinuousLevelTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_continuous_regular_measure_in_class]: supporting
    converse of the first observation of Federer 2.9.10, p. 157.
    Represented F1 levels make open sets measurable, finite F2
    hulls are Borel, and a unit cutoff over each bounded set gives
    finite mass there. The representing functional is specified by
    actual integral laws, without assuming the conclusion M. *)
Theorem bounded_continuous_regular_measure_in_class (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (lambda : (X -> R) -> R) :
  is_measure phi ->
  is_real_integral_functional phi (@bounded_support_continuous_functions R X) lambda ->
  is_function_lattice_regular (@bounded_support_continuous_functions R X) phi ->
  is_derivation_measure phi.
Proof.
move=> hm hrep hreg; constructor=> //.
- constructor.
  + move=> U hU; case: (pselect (U !=set0))=> [[a ha]|hzero].
    * apply: (@represented_lattice_increasing_level_measurable R X _ lambda phi hm hrep U).
      exact (@bounded_continuous_open_increasing_levels R X a U hU).
    * have he : U=set0.
        apply/seteqP; split=> x; [move=> hx; exfalso; apply: hzero; by exists x|by move=> []].
      rewrite he; exact: measure_measurable_empty hm.
  + move=> S; case: (ltP (phi S) +oo)=> hfin.
    * have [B [hSB [hB [he hBfin]]]] := (hreg S).1 hfin.
      exists B; split=> //; split=> //; exact: bounded_continuous_finite_hull_borel hB.
    * exists setT; split; first by move=> x _.
      split; first exact: open_borel_set openT.
      apply/eqP; rewrite eq_le (@measure_mono R X phi hm S setT (fun x _ => Logic.I)) andTb.
      have he : phi S=+oo by apply/eqP; rewrite eq_le leey andTb.
      by rewrite he leey.
- move=> A hAb.
  have [f [hf hon]] := @bounded_set_unit_test_exists R X A hAb.
  pose S := [set x | ((2%R : R)^-1<f x)%R].
  have hS : function_lattice_strict_levels (@bounded_support_continuous_functions R X) S.
    exists f,((2%R : R)^-1)%R; split=> //; split=> //; by rewrite invr_gt0 ltr0n.
  have hSf := @represented_lattice_strict_level_finite R X _ lambda phi hm hrep S hS.
  apply: le_lt_trans (@measure_mono R X phi hm A S _) hSf.
  move=> x hx; rewrite /S /= (hon x hx).
  by rewrite invf_lt1 ?ltr0n // ltr1n.
Qed.
