(** Federer (1969), 2.6.2, pp. 115–116: repeated integrability is preserved
    by decreasing intersections when the first repeated integral is finite.
    This application is stated for the P1 sequence used to build the
    enclosing set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureCountableClosure MeasureContinuityAbove
  MeasureIntegralUP MeasureSummableFiniteValues ProductMeasure ProductSections
  CountableRectangleUnionUP CountableRectangleFubini TotalBoundedIntegralLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [decreasing_rectangle_union_vertical_integral]: the
    decreasing P1 intersection step in Federer 2.6.2, pp. 115–116 The
    finite-first-measure condition is essential and retained. *)
Theorem decreasing_rectangle_union_vertical_integral (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (F : nat -> set (X * Y)) :
  (forall n, is_countable_rectangle_union alpha beta (F n)) ->
  (forall n m, (n <= m)%N -> F m `<=` F n) ->
  product_measure ha hb (F 0%N) < +oo ->
  is_measure_integral alpha
    (partial_function_total (fun x => beta (product_vertical_section (\bigcap_n F n) x)))
    (product_measure ha hb (\bigcap_n F n)).
Proof.
move=> hF hdec hfin.
pose nu := product_measure ha hb; have hnu := product_measure_is_measure ha hb.
pose u n x : extended_real_line R := beta (product_vertical_section (F n) x).
pose g x : extended_real_line R := beta (product_vertical_section (\bigcap_n F n) x).
have hi n : is_measure_integral alpha (partial_function_total (u n)) (nu (F n)).
  exact (@countable_rectangle_union_vertical_integral R X Y alpha beta ha hb (F n) (hF n)).
have hf0 : nu (F 0%N) \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hnu _)).
have hs : is_measure_summable alpha (partial_function_total (u 0%N)).
  exists (fine (nu (F 0%N))); rewrite fineK //; exact: hi.
have he := @measure_summable_finite_almost R X alpha ha _ hs.
have hsec n x : measure_measurable beta (product_vertical_section (F n) x).
  exact (@countable_rectangle_union_sections_measurable R X Y alpha beta hb (F n) (hF n) x).
have hsm n m x : (n <= m)%N -> product_vertical_section (F m) x `<=` product_vertical_section (F n) x.
  move=> hnm y hy; exact: hdec n m hnm (x,y) hy.
have hconv : measure_almost_everywhere alpha [set x | extended_order_limit (fun n => u n x) (g x)].
  apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ he)=> x [y [hy hyfin]].
  have hfirst : beta (product_vertical_section (F 0%N) x) < +oo.
    have hypos : 0 <= y by rewrite -(hy : u 0%N x = y); exact: measure_nonnegative.
    rewrite /u in hy; rewrite (hy : beta (product_vertical_section (F 0%N) x) = y).
    by move: hyfin; rewrite (ge0_fin_numE hypos).
  have hc := @measure_continuity_above R Y beta hb (fun n => product_vertical_section (F n) x)
    (fun n => hsec n x) (fun n m hnm => hsm n m x hnm) hfirst.
  exact: hc.2.
have hprod n : measure_measurable nu (F n).
  exact (@countable_rectangle_union_measurable R X Y alpha beta ha hb (F n) (hF n)).
have hlim := (@measure_continuity_above R (X * Y)%type nu hnu F hprod hdec hfin).2.
apply: (@total_nonnegative_bounded_integral_limit R X alpha ha u g (fun n => nu (F n)) _ _ _ hi hf0 hconv hlim).
- move=> n x; exact: measure_nonnegative.
- move=> n x; apply: (@measure_mono R Y beta hb _ _); exact: hsm 0%N n x (leq0n n).
Qed.
