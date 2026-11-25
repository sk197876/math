(** Federer (1969), 4.1.19, p. 377: scalar
    coefficient densities use the original L1
    duality and almost uniqueness. Countable
    measurability comes from the already proved
    compact exhaustion of the original open U;
    finite total measure is unnecessary. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  CountablyMeasurableUP CountablyMeasurableFunctions
  TotalScalarLpUP TotalEssentialNormBound RealLatticeDensityUP
  LpConjugatePair LpFunctionalDensityUP LpFunctionalDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_scalar_lone_density_full]:
    the bounded scalar densities used in Federer
    4.1.19, p. 377, have full L-infinity
    membership on the original countably measurable
    domain. Reuse 2.3.4, p. 76,
    and the original essential-norm bound of 2.4.12. *)
Theorem bounded_scalar_lone_density_full
    (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hCountable : measure_countably_measurable mu setT)
    (A : (X -> R) -> R) (k : X -> R) (c : R) :
  0 <= c -> is_real_lattice_density mu (total_scalar_lp mu 1) A k ->
  (forall x, `|k x| <= c) ->
  is_lp_functional_density mu 1 +oo A k /\
    (total_scalar_lp_norm mu +oo k <= c%:E)%E.
Proof.
move=> hC hK hBound.
have hAlmost : measure_almost_everywhere mu [set x | `|k x| <= c].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exact: hBound.
have hNorm := @total_essential_norm_bound R X mu hm k c hC hAlmost.
have hZero : @closed
    (real_norm_metric_space (scalar_absolute_value_norm R)) [set y | y = 0].
  change (closed [set (0 : real_norm_metric_space (scalar_absolute_value_norm R))]).
  apply: accessible_closed_set1; apply: hausdorff_accessible.
  exact: metric_hausdorff.
have hSupport := @countably_measurable_function_on_countable_source R X
  (real_norm_metric_space (scalar_absolute_value_norm R)) mu hm 0
  (total_scalar_function k) hZero hCountable hK.1.
split; last exact: hNorm.
split; last exact: hK.2.
split; first exact: leey.
split; first exact: hK.1.
split; last exact: hSupport.
exact: (le_lt_trans hNorm (ltry c)).
Qed.

(** Source for [bounded_scalar_lone_densities_almost_unique]:
    almost uniqueness of the scalar coefficient
    densities in Federer 4.1.19, p. 377,
    follows directly from the original L1-L-infinity
    duality, 2.5.7, pp. 98–99.
    The two displayed pointwise bounds may differ. *)
Theorem bounded_scalar_lone_densities_almost_unique
    (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hCountable : measure_countably_measurable mu setT)
    (A : (X -> R) -> R) (k l : X -> R) (c d : R) :
  0 <= c -> 0 <= d ->
  is_real_lattice_density mu (total_scalar_lp mu 1) A k ->
  is_real_lattice_density mu (total_scalar_lp mu 1) A l ->
  (forall x, `|k x| <= c) -> (forall x, `|l x| <= d) ->
  measure_almost_everywhere mu [set x | k x = l x].
Proof.
move=> hC hD hK hL hKBound hLBound.
have [hKFull hKNorm] := @bounded_scalar_lone_density_full R X mu hm
  hCountable A k c hC hK hKBound.
have [hLFull hLNorm] := @bounded_scalar_lone_density_full R X mu hm
  hCountable A l d hD hL hLBound.
have hConjugate : is_lp_conjugate_pair (1 : \bar R) +oo.
  by right; left.
exact: (@lp_functional_density_almost_unique R X mu hm 1 +oo A k l
  hConjugate hKFull hLFull).
Qed.
