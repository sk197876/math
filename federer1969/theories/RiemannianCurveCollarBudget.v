(** Federer (1969), 3.2.46, p. 281: both controlled
    endpoint collars contribute to the length lower bound.
    Keep the intervening curve segment, whose actual length
    is nonnegative, when splitting the full integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveSubinterval RiemannianCurveIntegralSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_curve_two_collar_budget]: the
    sum of the actual two collar lengths is bounded by the
    original full curve length, supporting the lower local
    comparison in Federer 3.2.46, p. 281. The middle
    interval is discarded only by proved nonnegativity. *)
Lemma riemannian_curve_two_collar_budget (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b u v :
  is_riemannian_admissible_curve A x y C a b -> a <= u -> u <= v -> v <= b ->
  (riemannian_curve_cost g C a u + riemannian_curve_cost g C v b <=
    riemannian_curve_cost g C a b)%E.
Proof.
move=> hC hau huv hvb.
have hub : u <= b := le_trans huv hvb.
have hav : a <= v := le_trans hau huv.
have hLeft := riemannian_admissible_curve_subinterval hC (lexx a) hau hub.
have hMiddle := riemannian_admissible_curve_subinterval hC hau huv hvb.
have hRight := riemannian_admissible_curve_subinterval hC hav hvb (lexx b).
have hTail := riemannian_admissible_curve_subinterval hC hau hub (lexx b).
have hCutU : a <= u <= b by rewrite hau hub.
have hCutV : u <= v <= b by rewrite huv hvb.
have hSplit := riemannian_curve_cost_split hg hC hCutU.
rewrite (riemannian_curve_cost_split hg hTail hCutV) in hSplit.
have hWholeE := riemannian_admissible_curve_cost_finite_value hg hC.
have hLeftE := riemannian_admissible_curve_cost_finite_value hg hLeft.
have hMiddleE := riemannian_admissible_curve_cost_finite_value hg hMiddle.
have hRightE := riemannian_admissible_curve_cost_finite_value hg hRight.
rewrite hWholeE hLeftE hMiddleE hRightE -!EFinD in hSplit.
have hReal : fine (riemannian_curve_cost g C a b) =
    fine (riemannian_curve_cost g C a u) +
      (fine (riemannian_curve_cost g C u v) + fine (riemannian_curve_cost g C v b)).
  by case: hSplit.
have hMid0 := riemannian_curve_cost_nonnegative g C u v.
rewrite hMiddleE lee_fin in hMid0.
rewrite hWholeE hLeftE hRightE -EFinD lee_fin hReal lerD2l lerDr.
exact: hMid0.
Qed.
