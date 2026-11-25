(** Federer (1969), 2.10.45, p. 203, last paragraph: if H^k(V)=0 then
    gamma=0. The cube estimate first gives zero on compact sets; a countable
    cover by relatively compact Euclidean balls gives zero everywhere. No
    measurability of V or U is needed in this case. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanAdditiveGroup EuclideanLebesgueHaar EuclideanCoordinateCubeLaws
  SquaredMetricProductUP HausdorffMeasure HausdorffProductSliceMeasure
  EuclideanCubeProductUpperBound MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_product_slice_null_factor]: direct
    zero-mass conclusion in 2.10.45, p. 203.
    The entire slice measure is zero, including on
    unbounded and nonmeasurable first-factor sets. This
    also covers an empty second factor and degree zero. *)
Theorem hausdorff_product_slice_null_factor (R : realType) m k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) (V : set Y) :
  hausdorff_measure k V=0%E -> forall U,
    hausdorff_product_slice_measure first second V (k+m) U=0%E.
Proof.
move=> hV.
pose gamma := hausdorff_product_slice_measure first second V (k+m).
have hm := @hausdorff_product_slice_is_measure R P
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] Y first second V (k+m).
have hfinite : (hausdorff_measure k V< +oo)%E by rewrite hV; exact: ltry.
have hcompact K (hK : compact K) : gamma K=0%E.
  have [r [hr hb]] := @euclidean_compact_coordinate_bound R m K hK.
  pose origin : R_n R m := [ffun _=> -r].
  pose Q : set (inner_metric_space (@euclidean_inner_productP R m)) :=
    [set x | forall i, -r<=x i<= -r+(r+r)].
  have ho i : origin i= -r by rewrite /origin ffunE.
  have hu : 0<=r+r by lra.
  have hQ := @euclidean_coordinate_cube_laws R m origin (-r) (r+r) ho hu.
  have hKQ : K `<=` Q.
    move=> x hx i; have hh := hb x hx i; move: hh; rewrite ler_norml=> /andP[hl hu']; apply/andP; split; lra.
  have hbound := @hausdorff_euclidean_cube_product_upper_bound R m k P Y pair first second hp
    origin (@coordinate_basis R m) Q (r+r) V hQ hu hfinite.
  rewrite hV mule0 in hbound.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  exact: le_trans (measure_mono hm hKQ) hbound.
have [hWo hWc hWT] := @euclidean_ball_cover R m.
have hball n : gamma (@euclidean_open_ball_sequence R m n)=0%E.
  have [C hC hWC] := hWc n.
  exact (@measure_null_subset R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)] gamma hm
    (@euclidean_open_ball_sequence R m n) C hWC (hcompact C hC)).
have hnull : gamma (\bigcup_n @euclidean_open_ball_sequence R m n)=0%E.
  exact (@measure_null_countable_union R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)] [the choiceType of (nat : Type)]
    gamma hm setT (@euclidean_open_ball_sequence R m) (countableP _) (fun n _=>hball n)).
move=> U; apply: (@measure_null_subset R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)] gamma hm
  U (\bigcup_n @euclidean_open_ball_sequence R m n) _ hnull)=> x _.
have [n hn] := hWT x; by exists n.
Qed.
