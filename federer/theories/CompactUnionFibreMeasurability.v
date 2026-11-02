(** Federer (1969), 2.10.26, pp. 189–190: supporting countable compact-union
    step after the compact case. Increasing compact sets give increasing
    fibre masses by continuity of measures 2.1.3(4), p. 55. Their supremum
    is measurable by the numerical-ray criterion 2.3.2(2), p. 73. Infinite
    masses are included. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit CountableOrderIntervals
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages HausdorffMeasure HausdorffFibreCutoffs
  CompactFibreMeasurability MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureCountableClosure MeasureContinuityBelow MeasurableFunctionUP MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [increasing_compact_fibre_mass_measurable]: supporting
    countable compact reduction in 2.10.26, p. 190.
    The fibre mass of an increasing compact union
    is measurable in the target Hausdorff measure,
    with no finite-mass or target-properness hypothesis. *)
Theorem increasing_compact_fibre_mass_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (K : nat -> set X) k m :
  continuous f -> (forall n, compact (K n)) ->
  (forall n j, (n<=j)%N -> K n `<=` K j) ->
  is_measure_measurable_function (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_mass f (\bigcup_n K n) k)).
Proof.
move=> hf hK hinc.
pose mu := @hausdorff_measure R Y m.
have hm : is_measure mu := @hausdorff_measure_is_measure R Y m.
pose L := \bigcup_n K n.
pose g := hausdorff_fibre_mass f L k.
pose w n := hausdorff_fibre_mass f (K n) k.
have hwm n : is_measure_measurable_function mu (partial_function_total (w n)).
  exact: compact_hausdorff_fibre_mass_measurable hf (hK n).
have hsource n y := compact_hausdorff_fibres_measurable k hf (hK n) y.
have hset y : (\bigcup_n (K n `&` f @^-1` [set y]))=L `&` f @^-1` [set y].
  apply/seteqP; split=> [x [n _ [hx hxy]]|x [[n _ hx] hxy]].
  - split=> //; by exists n.
  - exists n=> //; by split.
have hmass y : extended_increases_to (fun n=>w n y) (g y).
  have hh := @measure_continuity_below R X (@hausdorff_measure R X k)
    (@hausdorff_measure_is_measure R X k) (fun n=>K n `&` f @^-1` [set y]) (fun n=>hsource n y)
    (fun n j hnj x hx=>conj (hinc n j hnj x hx.1) hx.2).
  by rewrite hset in hh.
have hd : measure_almost_everywhere mu (partial_function_domain (partial_function_total g)).
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
apply/(measurable_extended_rational_upper_rays_iff hm hd)=> q.
have he : partial_function_preimage (partial_function_total g) [set z | (ratr q : R)%:E<z]=
    \bigcup_n partial_function_preimage (partial_function_total (w n)) [set z | (ratr q : R)%:E<z].
  rewrite partial_function_total_preimage; apply/seteqP; split.
  - move=> y hy; have [N hN] := (hmass y).2.1 _ hy.
    exists N=> //; exists (w N y); split=> //; exact: hN N (leqnn N).
  - move=> y [n _ [z [hz hqz]]].
    change (is_true ((ratr q : R)%:E<g y)).
    have hn : w n y<=g y.
      apply: (@measure_mono R X _ (@hausdorff_measure_is_measure R X k))=> x [hx hxy].
      split=> //; by exists n.
    rewrite -(hz : w n y=z) in hqz; exact: lt_le_trans hqz hn.
rewrite he; apply: (@measure_measurable_sequence_union R Y mu hm)=> n.
apply: (@measurable_function_open_preimage R Y (extended_real_line R) mu
  (partial_function_total (w n)) (hwm n)); exact: order_strict_upper_ray_open.
Qed.

(** Source for [countable_compact_union_fibres_measurable]: supporting
    fibre-set measurability in 2.10.26, p. 190.
    Each fibre of a countable compact union is a
    countable union of measurable compact fibres, even
    when the union has infinite Hausdorff measure. *)
Theorem countable_compact_union_fibres_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (K : nat -> set X) k :
  continuous f -> (forall n, compact (K n)) -> forall y,
  measure_measurable (@hausdorff_measure R X k) ((\bigcup_n K n) `&` f @^-1` [set y]).
Proof.
move=> hf hK y.
have he : ((\bigcup_n K n) `&` f @^-1` [set y])=\bigcup_n (K n `&` f @^-1` [set y]).
  apply/seteqP; split=> [x [[n _ hx] hxy]|x [n _ [hx hxy]]].
  - exists n=> //; by split.
  - split=> //; by exists n.
rewrite he; apply: (@measure_measurable_sequence_union R X _ (@hausdorff_measure_is_measure R X k))=> n.
exact: (@compact_hausdorff_fibres_measurable R X Y f (K n) k hf (hK n) y).
Qed.
