(** Federer (1969), 3.3.18, p. 301: the actual two-sided
    density strata on each original rectifiable carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP RegularMeasureUP
  TopologicalBorel BorelFamilyBasic BorelFunctionUP CountableOrderIntervals ExtendedRealOrderTopology
  MetricDensities MetricUpperDensityBorel FiniteUpperDensityHausdorffBound
  HausdorffUpperMetricDensity HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_rectifiable_density_stratum]: the original
    R_i in Federer 3.3.18, p. 301: intersect the original carrier
    R with the strict density band i inverse < Theta* < i. The
    independent definition adds no measurability or tangent assertion.
    A positive real bound is allowed in this supporting definition;
    the final countable assembly uses the printed positive integers. *)
Definition structure_rectifiable_density_stratum (R:realType) (X:metricType R) m
    (psi:set X->\bar R) (F:set X) (b:R):set X:=
  [set a|F a /\(b^-1%R%:E<upper_metric_density m psi a<b%:E)%E].

(** Source for [structure_rectifiable_density_stratum_borel]: the
    Borel assertion implicit in the R_i argument of Federer
    3.3.18, p. 301. Actual upper-density Borel measurability and
    the two original strict rays give the literal stratum. *)
Lemma structure_rectifiable_density_stratum_borel (R:realType) (X:metricType R) m
    (psi:set X->\bar R) (F:set X) (b:R):
  is_measure psi ->borel_set F ->borel_set (structure_rectifiable_density_stratum m psi F b).
Proof.
move=>hPsi hF.
have hBorel:=@metric_upper_density_borel R X m psi hPsi.
have hLower:borel_set [set a:X|b^-1%R%:E<upper_metric_density m psi a].
  exact:(hBorel [set u:extended_real_line R|b^-1%R%:E<u]
    (@order_strict_upper_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] b^-1%R%:E)).
have hUpper:borel_set [set a:X|upper_metric_density m psi a<b%:E].
  exact:(hBorel [set u:extended_real_line R|u<b%:E]
    (@order_strict_lower_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] b%:E)).
have hSet:structure_rectifiable_density_stratum m psi F b=
    F `&` ([set a:X|b^-1%R%:E<upper_metric_density m psi a] `&`
      [set a:X|upper_metric_density m psi a<b%:E]).
  apply/seteqP; split.
  - move=>a [ha /andP[hLowerAt hUpperAt]]; split; first exact:ha.
    by split.
  - move=>a [ha [hLowerAt hUpperAt]]; split; first exact:ha.
    by apply/andP.
rewrite hSet.
apply:(borel_family_binary_intersection (borel_sets_family X) hF).
exact:(borel_family_binary_intersection (borel_sets_family X) hLower hUpper).
Qed.

(** Source for [structure_rectifiable_density_stratum_comparisons]:
    BOTH printed inequalities for EVERY original S subset of R_i
    in Federer 3.3.18, p. 301. Actual 2.10.19(3) and finite
    regular open approximation give the lower comparison. Actual
    2.10.19(1) gives the upper comparison. No measurability of the
    tested original subset S or supplied comparison is assumed. *)
Theorem structure_rectifiable_density_stratum_comparisons (R:realType) (X:metricType R) m
    (psi:set X->\bar R) (F S:set X) (b:R):
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->(0<b)%R ->
  S `<=` structure_rectifiable_density_stratum m psi F b ->
  b^-1%R%:E*@hausdorff_measure R X m S<=psi S /\
    psi S<=(2^+m*b)%R%:E*@hausdorff_measure R X m S.
Proof.
move=>hPsi hRegular hFinite hb hSub.
have hInverse:(0<b^-1)%R by rewrite invr_gt0.
have hLow a:S a ->b^-1%R%:E<upper_metric_density m psi a.
  move=>ha; exact:(andP (hSub a ha).2).1.
have hHigh a:S a ->upper_metric_density m psi a<b%:E.
  move=>ha; exact:(andP (hSub a ha).2).2.
have hHBound:=@finite_upper_density_hausdorff_bound R X m psi S b^-1%R
  hPsi hRegular hFinite hInverse hLow.
rewrite invrK in hHBound.
split.
- have hInverseE:(0<=b^-1%R%:E)%E by rewrite lee_fin; exact:ltW hInverse.
  have hScale:=lee_wpmul2l hInverseE hHBound.
  rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in hScale.
  exact:hScale.
- exact:(@hausdorff_upper_metric_density_bound R X m psi S b hPsi
    (borel_regular_is_regular hPsi hRegular) hb hHigh).
Qed.
