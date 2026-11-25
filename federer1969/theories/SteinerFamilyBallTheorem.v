(** Federer (1969), 2.10.31, pp. 195–196: a nonempty Hausdorff-closed class
    of nonempty compact Euclidean sets, stable under every Steiner
    hyperplane symmetrisation, contains the origin singleton or a
    positive-radius closed ball centred at zero. The metric carrier records
    compactness and nonemptiness; closedness and stability retain their full
    printed meanings. The proof first gives the general proper
    inner-product-space version, then the exact Euclidean instance,
    including dimension zero. Federer's May 1987 erratum p. 4, book p. 195
    line 20, only corrects punctuation in the statement; it has no
    correction for the proof's printed B(a,s) on p. 196. Our local
    centre-zero correction is proved and documented separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology EuclideanAdditiveGroup CompactSetDistanceProfile CompactHausdorffMetric
  MetricClosedBalls LipschitzFunctionCompact CompactEnclosingRadius CompactEnclosingRadiusZero
  CompactFamilyMinimumRadius SteinerStableFamilyUP SteinerMinimalBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_closed_family_contains_ball]: direct
    proof of 2.10.31, pp. 195–196, stated
    first in any boundedly compact real inner-product
    space. Radius zero and positive radius are
    distinguished, without a dimensional hypothesis. *)
Theorem steiner_closed_family_contains_ball (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB))) :
  metric_boundedly_compact (inner_metric_space hB) -> C !=set0 -> closed C ->
  is_steiner_stable_family hB C ->
  exists S : compact_hausdorff_space (inner_metric_space hB), C S /\
    (val S=[set (0 : inner_metric_space hB)] \/
      exists r : R, 0<r /\ val S=metric_closed_ball (0 : inner_metric_space hB) r).
Proof.
move=> hX hne hc hC.
have [S [hS hmin]] := closed_compact_family_minimum_radius (0 : inner_metric_space hB) hX hne hc.
exists S; split=> //.
pose r := compact_enclosing_radius (0 : inner_metric_space hB) S.
case: (eqVneq r 0)=> [hr0|hr0].
- left; exact (compact_enclosing_radius_zero_singleton hr0).
- have hr : 0<r.
    rewrite lt_neqAle eq_sym hr0 /=; exact: compact_enclosing_radius_nonnegative.
  right; exists r; split=> //.
  exact (steiner_positive_minimiser_is_ball hX hC hS hmin hr).
Qed.

(** Source for [federer_2_10_31]: direct Euclidean theorem
    2.10.31, pp. 195–196, with bold B
    interpreted as the closed ball. All unit normals
    occur in the stability predicate; normal choice
    independence was established in 2.10.30.
    The zero-dimensional case is included. *)
Theorem federer_2_10_31 (R : realType) (n : nat)
    (C : set (compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))) :
  C !=set0 -> closed C -> is_steiner_stable_family (@euclidean_inner_productP R n) C ->
  exists S : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)), C S /\
    (val S=[set (0 : inner_metric_space (@euclidean_inner_productP R n))] \/
      exists r : R, 0<r /\ val S=metric_closed_ball
        (0 : inner_metric_space (@euclidean_inner_productP R n)) r).
Proof.
apply: steiner_closed_family_contains_ball.
move=> a r _.
have he : metric_closed_ball a r=[set x | `|x-a|<=r].
  by apply/seteqP; split=> x; rewrite /metric_closed_ball /= inner_metric_normE.
rewrite he; exact: euclidean_closed_ball_compact.
Qed.
