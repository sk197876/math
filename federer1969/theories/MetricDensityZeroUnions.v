(** Federer (1969), 3.2.16, pp. 252–253:
    subset and finite-union laws for zero m-density
    exceptional sets. They are proved for arbitrary
    measures, without positive finite ball masses. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureSplit
  MeasureRestriction MetricClosedBalls MetricDensities MetricDensityZero
  MetricDensityNumericalBounds EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_restricted_density_zero_empty]:
    the empty exceptional set in the density tests
    of Federer 3.2.16, pp. 252–253. *)
Lemma metric_restricted_density_zero_empty (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) a :
  is_measure mu ->
  partial_function_graph (metric_density m (measure_restrict mu set0)) a 0.
Proof.
move=> hm.
have hnu := measure_restrict_is_measure hm (@set0 X).
apply: (@metric_density_zero_iff_upper_zero R X m _ a hnu).2.
apply: (@metric_upper_density_zero_iff_small R X m _ a hnu).2=> e he.
exists 1%R; split; first exact: ltr01.
move=> r hr.
rewrite /metric_ball_density /measure_restrict set0I (measure_empty hm) mul0e lee_fin.
exact: ltW he.
Qed.

(** Source for [metric_restricted_density_zero_subset]:
    inclusion of zero-density exceptional sets in
    Federer 3.2.16, pp. 252–253. Neither
    subset is required to be measurable. *)
Lemma metric_restricted_density_zero_subset (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) (A B : set X) a :
  is_measure mu -> A `<=` B ->
  partial_function_graph (metric_density m (measure_restrict mu B)) a 0 ->
  partial_function_graph (metric_density m (measure_restrict mu A)) a 0.
Proof.
move=> hm hAB hB; apply: (metric_restricted_density_zero_local_mono hm _ hB).
exists 1%R; split; first exact: ltr01.
by move=> x hx hA; exact: hAB x hA.
Qed.

(** Source for [metric_restricted_density_zero_union]:
    the finite-union step in the compact-cone and
    common-agreement arguments of Federer 3.2.16,
    pp. 252–253. Small normalized masses are
    bounded at half the requested tolerance. *)
Theorem metric_restricted_density_zero_union (R : realType)
    (X : metricType R) m (mu : set X -> \bar R) (A B : set X) a :
  is_measure mu ->
  partial_function_graph (metric_density m (measure_restrict mu A)) a 0 ->
  partial_function_graph (metric_density m (measure_restrict mu B)) a 0 ->
  partial_function_graph (metric_density m (measure_restrict mu (A `|` B))) a 0.
Proof.
move=> hm hA hB.
pose nuA := measure_restrict mu A.
pose nuB := measure_restrict mu B.
pose nuU := measure_restrict mu (A `|` B).
have hmA := measure_restrict_is_measure hm A.
have hmB := measure_restrict_is_measure hm B.
have hmU := measure_restrict_is_measure hm (A `|` B).
apply: (@metric_density_zero_iff_upper_zero R X m nuU a hmU).2.
apply: (@metric_upper_density_zero_iff_small R X m nuU a hmU).2=> e he.
have he2 : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have hAu := (@metric_density_zero_iff_upper_zero R X m nuA a hmA).1 hA.
have hBu := (@metric_density_zero_iff_upper_zero R X m nuB a hmB).1 hB.
have [d [hd hAs]] := (@metric_upper_density_zero_iff_small R X m nuA a hmA).1 hAu _ he2.
have [s [hs hBs]] := (@metric_upper_density_zero_iff_small R X m nuB a hmB).1 hBu _ he2.
exists (Num.min d s)%R; split; first by rewrite lt_min hd hs.
move=> r /andP [hr hmin].
have hrd : (r<d)%R.
  apply: lt_le_trans hmin _; by rewrite ge_min lexx.
have hrs : (r<s)%R.
  apply: lt_le_trans hmin _; by rewrite ge_min lexx orbT.
have hAr : (0<r<d)%R by apply/andP; split.
have hBr : (0<r<s)%R by apply/andP; split.
pose K := metric_closed_ball a r.
have hnum : nuU K<=nuA K+nuB K.
  apply: (@measure_binary_cover R X mu hm ((A `|` B) `&` K) (A `&` K) (B `&` K)).
  by move=> x [[hx|hx] hk]; [left|right]; split.
pose c := ((euclidean_unit_ball_volume R m*r^+m)%R%:E)^-1.
have hc : 0<=c.
  rewrite /c inve_ge0 lee_fin; exact: ltW (metric_ball_density_denominator_positive m hr).
have hball : metric_ball_density m nuU a r<=
    metric_ball_density m nuA a r+metric_ball_density m nuB a r.
  have hh := lee_wpmul2r hc hnum.
  rewrite (@ge0_muleDl R c (nuA K) (nuB K)
    (@measure_nonnegative R X nuA hmA K) (@measure_nonnegative R X nuB hmB K)) in hh.
  exact hh.
have hsum := leeD (hAs r hAr) (hBs r hBr).
have hsplit : ((e/2)%R)%:E+((e/2)%R)%:E=e%:E by rewrite -EFinD -splitr.
rewrite hsplit in hsum; exact: le_trans hball hsum.
Qed.

(** Source for [metric_restricted_density_zero_finite_union]:
    the finite family covering the directional cone
    in Federer 3.2.16, p. 253. Empty
    covering families are included. *)
Lemma metric_restricted_density_zero_finite_union (R : realType)
    (X : metricType R) (J : choiceType) m (mu : set X -> \bar R)
    (F : {fset J}) (S : J -> set X) a :
  is_measure mu ->
  (forall j, j \in F -> partial_function_graph (metric_density m (measure_restrict mu (S j))) a 0) ->
  partial_function_graph (metric_density m
    (measure_restrict mu (\bigcup_(j in [set j | j \in F]) S j))) a 0.
Proof.
move=> hm hF; rewrite bigcup_fset big_seq.
apply: (big_ind (fun E : set X =>
  partial_function_graph (metric_density m (measure_restrict mu E)) a 0)).
- exact: metric_restricted_density_zero_empty hm.
- move=> A B hA hB; exact: (metric_restricted_density_zero_union hm hA hB).
- move=> j hj; exact: hF j hj.
Qed.
