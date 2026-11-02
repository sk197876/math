(** Federer (1969), 2.10.36, printed p. 198: the two-apex hull has volume at
    least full height times base volume divided by ambient dimension. Reduce
    a positive half-height r to one using a first-coordinate diagonal map.
    Its determinant and volume factor are proved from 2.7.16(1), pp.
    134–135. The map is local proof data; all mathematical objects use their
    existing public interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  ScalarConvexLength EuclideanCoordinateSplit EuclideanLinearMaps EuclideanLebesgueDeterminant EuclideanLebesgueDimensions
  UnitBipyramidVolumeBound MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bipyramid_height_volume_lower_bound]: supporting
    positive-height version of the last
    volume comparison in 2.10.36, p. 198.
    The enclosing compact convex set contains
    the base at height zero and
    the two apex points at heights
    r and -r. The base need
    only have finite outer volume. *)
Theorem bipyramid_height_volume_lower_bound (R : realType) (n : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (C : set (inner_metric_space (@euclidean_inner_productP R n.+1)))
    (z : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<r -> compact C -> is_inner_convex C -> (euclidean_lebesgue_measure n K< +oo)%E ->
  (forall x, K x -> C (euclidean_join (x,0))) ->
  C (euclidean_join (z,r)) -> C (euclidean_join (z,-r)) ->
  (((2*r*n.+1%:R^-1)%R%:E)*euclidean_lebesgue_measure n K<=euclidean_lebesgue_measure n.+1 C)%E.
Proof.
move=> hr hC hconv hK hbase hplus hminus.
pose c (i : 'I_n.+1) : R := if i==ord0 then r^-1 else 1.
pose D := @euclidean_diagonal_map R n.+1 c.
have hjoin (x : inner_metric_space (@euclidean_inner_productP R n)) (t : R) :
    D (euclidean_join (x,t))=euclidean_join (x,r^-1*t).
  apply/ffunP=> i; rewrite /D /euclidean_diagonal_map /euclidean_diagonal ffunE.
  case: (unliftP ord0 i)=> [j ->|->].
  - by rewrite /c lift_eqF mul1r !euclidean_join_tail.
  - by rewrite /c eqxx !euclidean_join_head.
have hdet : euclidean_det D=r^-1.
  rewrite /D euclidean_diagonal_det (bigD1 ord0) // /c eqxx.
  have he : (\prod_(i : 'I_n.+1 | i!=ord0) (if i==ord0 then r^-1 else 1))= 1.
    apply: big1=> i hi; by rewrite (negbTE hi).
  rewrite he.
  change ((r^-1 : R)*1=r^-1).
  exact: mulr1.
pose U : set (inner_metric_space (@euclidean_inner_productP R n.+1)) := D @` C.
have hUc : compact U.
  apply: continuous_compact hC.
  apply: continuous_subspaceT; exact: euclidean_linear_continuous.
have hUm : measure_measurable (@euclidean_lebesgue_measure R n.+1) U.
  apply: (borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n.+1)
    (euclidean_lebesgue_borel_regular R n.+1)).
  apply: closed_borel_set; exact: compact_closed (@metric_hausdorff R
    (inner_metric_space (@euclidean_inner_productP R n.+1))) hUc.
have hUv : is_inner_convex U := linear_image_inner_convex hconv.
have hUb x : K x -> U (euclidean_join (x,0)).
  move=> hx; exists (euclidean_join (x,0)); first exact: hbase.
  by rewrite hjoin mulr0.
have hr0 : r!=0 by rewrite gt_eqF.
have hUp : U (euclidean_join (z,1)).
  exists (euclidean_join (z,r))=> //; by rewrite hjoin mulVf.
have hUn : U (euclidean_join (z,-1)).
  exists (euclidean_join (z,-r))=> //; by rewrite hjoin mulrN mulVf.
have hh := @unit_bipyramid_volume_lower_bound R n K U z hUv hUm hK hUb hUp hUn.
have hri : 0<=r^-1 by rewrite invr_ge0; exact: ltW hr.
have hvol : euclidean_lebesgue_measure n.+1 U=
    ((r^-1)%R%:E*euclidean_lebesgue_measure n.+1 C)%E.
  by rewrite /U euclidean_lebesgue_linear_image hdet (ger0_norm hri).
rewrite hvol in hh.
have hrE : (0<=r%:E)%E by rewrite lee_fin; exact: ltW hr.
have hb := lee_wpmul2l hrE hh.
rewrite !muleA -!EFinM mulfV // mul1e in hb.
have he : r*(2*n.+1%:R^-1)= 2*r*n.+1%:R^-1 by ring.
by rewrite he in hb.
Qed.
