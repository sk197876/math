(** Federer (1969), 2.10.26, pp. 189–190: null-source-mass reduction in a
    boundedly compact source and an arbitrary metric target. Cover the
    source by compact closed balls; each image is compact, so 2.10.25
    applies in its induced compact metric codomain. A common conull region
    and countable subadditivity finish the null-fibre conclusion. This
    expands the reduction on p. 190 and checks the alternative hypothesis of
    2.10.25. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffFibreCutoffs NullFibresProperSource RealNullFibresCompactImage ExtendedRealOrderTopology LipschitzUP NormMetricScaleContinuity
  MetricClosedBalls LipschitzFunctionCompact HausdorffMeasure HausdorffFibreCutoffs NullFibresCompactImage
  MeasureUP MeasureBasic MeasureIndexedCover MeasureAlmostUP MeasureAlmostBasic NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_real_hausdorff_fibres_proper_source]: direct
    zero-source-mass case of 2.10.26, p. 190,
    with the printed boundedly compact source and
    arbitrary metric target. A common target-null
    exceptional set handles every source ball. *)
Theorem null_real_hausdorff_fibres_proper_source (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (A : set X) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  metric_boundedly_compact X -> is_metric_lipschitz_bound setT f L ->
  @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A=0 ->
  measure_almost_everywhere (@real_hausdorff_measure R Y m hm) [set y | real_hausdorff_fibre_mass f A hk y=0].
Proof.
move=> hX hf hA0.
have hMeasure := @real_hausdorff_measure_is_measure R Y m hm.
case: (pselect (A!=set0))=> [[a ha]|hempty]; last first.
  have hA : A=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  apply: (@measure_almost_everywhere_mono R Y _ hMeasure setT _ _ (measure_almost_everywhere_true hMeasure))=> y _.
  change (real_hausdorff_fibre_mass f A hk y=0).
  rewrite /real_hausdorff_fibre_mass hA set0I; exact: measure_empty (@real_hausdorff_measure_is_measure R X k hk).
pose B n := metric_closed_ball a (n%:R : R).
pose C n := A `&` B n.
have hB n : compact (B n) := hX a _ (@ler0n R n).
have hcont : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L hf.1)=> x z.
  exact: hf.2 x z Logic.I Logic.I.
have hC0 n : @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) (C n)=0.
  apply: (@measure_null_subset R X _ (@real_hausdorff_measure_is_measure R X (k+m)%R (addr_ge0 hk hm)) _ A _ hA0).
  by move=> x [hx _].
have hn n : measure_almost_everywhere (@real_hausdorff_measure R Y m hm)
    [set y | real_hausdorff_fibre_mass f (C n) hk y=0].
  apply: (@null_real_hausdorff_fibres_compact_image R X Y f L (C n) (f @` B n) k m hk hm hf
    (continuous_compact (continuous_subspaceT hcont) (hB n)) _ (hC0 n)).
  move=> y [x [_ hxB] <-]; by exists x.
have hall := @measure_almost_everywhere_countable R Y [the choiceType of (nat : Type)]
  (@real_hausdorff_measure R Y m hm) hMeasure setT (fun n=>[set y | real_hausdorff_fibre_mass f (C n) hk y=0])
  (countableP _) (fun n _=>hn n).
apply: (@measure_almost_everywhere_mono R Y _ hMeasure _ _ _ hall)=> y hy.
have hcover : (A `&` f @^-1` [set y]) `<=` \bigcup_n (C n `&` f @^-1` [set y]).
  move=> x [hx hxy]; have [n _ hxb] := @metric_natural_closed_balls_cover R X a x Logic.I.
  exists n=> //; by split=> //; split.
have hh := @measure_indexed_cover R X [the choiceType of (nat : Type)] (@real_hausdorff_measure R X k hk)
  (@real_hausdorff_measure_is_measure R X k hk) _ setT _ (countableP _) hcover.
have hsum : nonnegative_sum setT (fun n=>@real_hausdorff_measure R X k hk (C n `&` f @^-1` [set y]))=0.
  apply: nonnegative_sum_zero=> n _; exact: hy n Logic.I.
rewrite hsum in hh.
change (real_hausdorff_fibre_mass f A hk y=0); rewrite /real_hausdorff_fibre_mass.
apply/eqP; rewrite eq_le hh /=.
exact: (@measure_nonnegative R X (@real_hausdorff_measure R X k hk)
  (@real_hausdorff_measure_is_measure R X k hk) (A `&` f @^-1` [set y])).
Qed.
