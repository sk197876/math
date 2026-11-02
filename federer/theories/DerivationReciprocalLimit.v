(** The reciprocal-limit implication in Federer (1969), 2.9.4, p. 154.
    Choose a finite threshold strictly between c and the upper limit.
    Arbitrarily small bounded cells have forward ratio above that threshold,
    hence reverse ratio below its reciprocal. The lower limit is bounded by
    that smaller reciprocal. this module retains Federer's strict
    implication. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureDerivates
  MeasureUP MeasureBasic CoveringRelationLimits CoveringUpperValues
  FiniteMeasureRatioReversal ExtendedRealOrderTopology MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_strict_reciprocal_limit]: direct
    final implication in the proof of Federer 2.9.4,
    p. 154: upper V limit of psi/phi
    greater than c entails lower V limit of phi/psi
    less than 1/c. Bounded auxiliary cells justify
    inversion of the original partial quotient. *)
Lemma derivation_strict_reciprocal_limit (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) x (c : R) :
  is_derivation_measure psi -> is_derivation_measure phi -> (0<c)%R ->
  c%:E<covering_upper_limit V (measure_ratio_function psi phi) x ->
  covering_lower_limit V (measure_ratio_function phi psi) x<(c^-1)%:E.
Proof.
move=> hpsi hphi hc hup.
have [q [hcq hqu]] := @extended_rationals_order_dense R c%:E
  (covering_upper_limit V (measure_ratio_function psi phi) x) hup.
pose d := (ratr q : R).
have hcd : (c<d)%R by move: hcq; rewrite lte_fin.
have hd : (0<d)%R := lt_trans hc hcd.
have hlow : covering_lower_limit V (measure_ratio_function phi psi) x<=(d^-1)%:E.
  apply: covering_lower_limit_bound_by_small_values=> e he.
  pose t := (Num.min e 1)%R.
  have ht : (0<t)%R by rewrite /t lt_min he ltr01.
  have [S [y [hS [hdiam [hy hdy]]]]] :=
    @covering_upper_limit_large_value R X V (measure_ratio_function psi phi) x d%:E t hqu ht.
  have hdiam1 : extended_metric_diameter S<1.
    apply: lt_le_trans hdiam _; by rewrite lee_fin /t ge_min lexx orbT.
  have hbounded : metric_set_bounded S := lt_trans hdiam1 (@ltry R 1%R).
  have haf : psi S \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative (derivation_measure_law hpsi) S)).
    exact: derivation_measure_bounded_finite hpsi S hbounded.
  have hbf : phi S \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative (derivation_measure_law hphi) S)).
    exact: derivation_measure_bounded_finite hphi S hbounded.
  have [z [hz hzd]] := @finite_measure_ratio_reversal R X psi phi S d y haf hbf
    (measure_nonnegative (derivation_measure_law hphi) S) hd hy hdy.
  exists S,z; split=> //; split.
  - apply: lt_le_trans hdiam _; by rewrite lee_fin /t ge_min lexx.
  - split=> //; exact: ltW hzd.
apply: le_lt_trans hlow _; rewrite lte_fin.
by rewrite ltr_pV2 // !inE unitfE ?gt_eqF //; exact: hd || exact: hc.
Qed.
