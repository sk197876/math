(** Supporting transfer argument for the equality of compact-test integrals
    in Federer (1969), 2.5.14, pp. 107–108. The defining finite F2 hulls
    from 2.5.3 show that a dominated measure agreeing on level families
    agrees on every finite measurable set and preserves its measurability.
    This spells out a local proof route, rather than importing the later
    integral criterion cited. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import FunctionLatticeLevelFamilies FunctionLatticeRegularityUP
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableClosure MeasureContinuityAbove
  ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum FiniteMeasurableDifferenceValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lattice_finite_hull_measure_transfer]: agreement
    on F1 passes to finite F2 intersections, using 2.1.3(5),
    p. 55, and 2.5.3, p. 94, to support the
    representation assertion in Federer 2.5.14, p. 107.
    The finite first-set condition is explicitly retained. *)
Lemma lattice_finite_hull_measure_transfer (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu) :
  (forall V, function_lattice_increasing_levels L V ->
    measure_measurable mu V /\ measure_measurable nu V /\ nu V=mu V) ->
  forall W, function_lattice_finite_hulls L mu W -> measure_measurable nu W /\ nu W=mu W.
Proof.
move=> h1 W [V [hV [hmono [hfin ->]]]].
have hmu n := (h1 _ (hV n)).1.
have hnu n := (h1 _ (hV n)).2.1.
have hv0 : nu (V 0%N) < +oo by rewrite (h1 _ (hV 0%N)).2.2.
have hlimu := @measure_continuity_above R X mu hm V hmu hmono hfin.
have hlimv := @measure_continuity_above R X nu hn V hnu hmono hv0.
split.
- apply: (@measure_measurable_countable_intersection R X nat nu hn setT V (countableP _))=> n _; exact: hnu.
- have he : (fun n => nu (V n))=(fun n => mu (V n)).
    apply: funext=> n; exact: (h1 _ (hV n)).2.2.
  rewrite he in hlimv; exact: extended_order_limit_unique hlimv.2 hlimu.2.
Qed.

(** Source for [lattice_regular_finite_measure_transfer]: supporting
    preservation of finite measurable sets for the representing Radon
    measure in Federer 2.5.14, pp. 107–108. This consequence is proved from
    the F2 hull definition of 2.5.3, p. 94, and domination; it is not
    claimed as an identical separately numbered result. *)
Theorem lattice_regular_finite_measure_transfer (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu) :
  is_function_lattice_regular L mu -> (forall S, nu S <= mu S) ->
  (forall W, function_lattice_finite_hulls L mu W -> measure_measurable nu W /\ nu W=mu W) ->
  forall S, measure_measurable mu S -> mu S < +oo -> measure_measurable nu S /\ nu S=mu S.
Proof.
move=> hr hdom h2 S hS hfin.
have [W [hSW [hW [hval hWfin]]]] := (hr S).1 hfin.
have [hWn hWval] := h2 W hW.
have hz : mu (W `\` S)=0.
  by rewrite (@finite_measurable_difference_value R X mu hm W S hS hSW hWfin) hval subrr.
have hzn : nu (W `\` S)=0.
  apply/eqP; rewrite eq_le (@measure_nonnegative R X nu hn _) andbT.
  by have h := hdom (W `\` S); rewrite hz in h.
have hSn : measure_measurable nu S.
  have he : S=W `\` (W `\` S).
    apply/seteqP; split.
    + move=> x hx; split; first exact: hSW x hx.
      by move=> [_ hns]; exact: hns hx.
    + move=> x [hx hnS]; apply: contrapT=> hns; apply: hnS; by split.
  rewrite he; exact (@measure_measurable_difference R X nu hn W (W `\` S) hWn (measure_null_measurable hn hzn)).
split=> //.
have hi : W `&` S=S.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hSW x hx.
have he := hSn W; rewrite hi hzn adde0 in he.
by rewrite -he hWval -hval.
Qed.
