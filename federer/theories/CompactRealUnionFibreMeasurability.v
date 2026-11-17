(** Federer (1969), 2.10.26, pp. 189–190: supporting countable compact-union
    step after the compact case. Increasing compact sets give increasing
    fibre masses by continuity of measures 2.1.3(4), p. 55. Their supremum
    is measurable by the numerical-ray criterion 2.3.2(2), p. 73. Infinite
    masses are included. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffFibreCutoffs ExtendedRealOrderTopology ExtendedRealOrderLimit CountableOrderIntervals
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages HausdorffMeasure HausdorffFibreCutoffs
  CompactRealFibreMeasurability MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureCountableClosure MeasureContinuityBelow MeasurableFunctionUP MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [increasing_compact_real_fibre_mass_measurable]: supporting
    countable compact reduction in 2.10.26, p. 190.
    The fibre mass of an increasing compact union
    is measurable in the target Hausdorff measure,
    with no finite-mass or target-properness hypothesis. *)
Theorem increasing_compact_real_fibre_mass_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (K : nat -> set X) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  continuous f -> (forall n, compact (K n)) ->
  (forall n j, (n<=j)%N -> K n `<=` K j) ->
  is_measure_measurable_function (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_fibre_mass f (\bigcup_n K n) hk)).
Proof.
move=> hf hK hinc.
pose mu := @real_hausdorff_measure R Y m hm.
have hMu : is_measure mu := @real_hausdorff_measure_is_measure R Y m hm.
pose L := \bigcup_n K n.
pose g := real_hausdorff_fibre_mass f L hk.
pose w n := real_hausdorff_fibre_mass f (K n) hk.
have hwm n : is_measure_measurable_function mu (partial_function_total (w n)).
  exact: compact_real_hausdorff_fibre_mass_measurable hf (hK n).
have hsource n y := compact_real_hausdorff_fibres_measurable hk hf (hK n) y.
have hset y : (\bigcup_n (K n `&` f @^-1` [set y]))=L `&` f @^-1` [set y].
  apply/seteqP; split=> [x [n _ [hx hxy]]|x [[n _ hx] hxy]].
  - split=> //; by exists n.
  - exists n=> //; by split.
have hmass y : extended_increases_to (fun n=>w n y) (g y).
  have hh := @measure_continuity_below R X (@real_hausdorff_measure R X k hk)
    (@real_hausdorff_measure_is_measure R X k hk) (fun n=>K n `&` f @^-1` [set y]) (fun n=>hsource n y)
    (fun n j hnj x hx=>conj (hinc n j hnj x hx.1) hx.2).
  by rewrite hset in hh.
have hd : measure_almost_everywhere mu (partial_function_domain (partial_function_total g)).
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hMu.
apply/(measurable_extended_rational_upper_rays_iff hMu hd)=> q.
have he : partial_function_preimage (partial_function_total g) [set z | (ratr q : R)%:E<z]=
    \bigcup_n partial_function_preimage (partial_function_total (w n)) [set z | (ratr q : R)%:E<z].
  rewrite partial_function_total_preimage; apply/seteqP; split.
  - move=> y hy; have [N hN] := (hmass y).2.1 _ hy.
    exists N=> //; exists (w N y); split=> //; exact: hN N (leqnn N).
  - move=> y [n _ [z [hz hqz]]].
    change (is_true ((ratr q : R)%:E<g y)).
    have hn : w n y<=g y.
      apply: (@measure_mono R X _ (@real_hausdorff_measure_is_measure R X k hk))=> x [hx hxy].
      split=> //; by exists n.
    rewrite -(hz : w n y=z) in hqz; exact: lt_le_trans hqz hn.
rewrite he; apply: (@measure_measurable_sequence_union R Y mu hMu)=> n.
apply: (@measurable_function_open_preimage R Y (extended_real_line R) mu
  (partial_function_total (w n)) (hwm n)); exact: order_strict_upper_ray_open.
Qed.

(** Source for [countable_compact_real_union_fibres_measurable]: supporting
    fibre-set measurability in 2.10.26, p. 190.
    Each fibre of a countable compact union is a
    countable union of measurable compact fibres, even
    when the union has infinite Hausdorff measure. *)
Theorem countable_compact_real_union_fibres_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (K : nat -> set X) (k : R) (hk : (0<=k)%R) :
  continuous f -> (forall n, compact (K n)) -> forall y,
  measure_measurable (@real_hausdorff_measure R X k hk) ((\bigcup_n K n) `&` f @^-1` [set y]).
Proof.
move=> hf hK y.
have he : ((\bigcup_n K n) `&` f @^-1` [set y])=\bigcup_n (K n `&` f @^-1` [set y]).
  apply/seteqP; split=> [x [[n _ hx] hxy]|x [n _ [hx hxy]]].
  - exists n=> //; by split.
  - split=> //; by exists n.
rewrite he; apply: (@measure_measurable_sequence_union R X _ (@real_hausdorff_measure_is_measure R X k hk))=> n.
exact: (@compact_real_hausdorff_fibres_measurable R X Y f (K n) k hk hf (hK n) y).
Qed.
