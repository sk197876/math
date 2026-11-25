(** Federer (1969), 3.2.46, p. 281: the original
    Lipschitz curve may be restricted to subintervals when
    comparing lengths and treating curves that leave a local
    comparison neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground LipschitzUP RiemannianCurveCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_admissible_curve_subinterval]:
    each actual subinterval supplies another admissible curve
    in Federer 3.2.46, p. 281. The map, its values and the
    interval Lipschitz bound are unchanged. *)
Lemma riemannian_admissible_curve_subinterval (R : realType) n A x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b u v :
  is_riemannian_admissible_curve A x y C a b ->
  a <= u -> u <= v -> v <= b ->
  is_riemannian_admissible_curve A (C u) (C v) C u v.
Proof.
move=> [hab [[L [hL hBound]] [hImage [hStart hEnd]]]] hau huv hvb.
have hSubset t : u <= t <= v -> a <= t <= b.
  move=> /andP [hut htv]; apply/andP; split.
  - exact: le_trans hau hut.
  - exact: le_trans htv hvb.
split; first exact: huv; split.
- exists L; split=> //; split; first exact: hBound.1.
  move=> t s ht hs.
  apply: hBound.2.
  + by rewrite /mkset in_itv /=; apply: hSubset; move: ht; rewrite /mkset in_itv /=.
  + by rewrite /mkset in_itv /=; apply: hSubset; move: hs; rewrite /mkset in_itv /=.
- split; first by move=> t ht; exact: hImage (hSubset t ht).
  by split.
Qed.
