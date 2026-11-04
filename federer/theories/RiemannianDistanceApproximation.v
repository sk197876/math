(** Federer (1969), 3.2.46, p. 281: a finite infimum
    of the actual admissible curve lengths can be approached
    by such lengths. This is an order consequence of the
    independent infimum laws, not a minimizing-curve axiom. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianCurveCost RiemannianDistanceUP RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_distance_finite_approximation]:
    the defining infimum in Federer 3.2.46, p. 281, admits
    an actual curve within every positive error when its value
    is finite. No geodesic or chosen global path is required. *)
Lemma riemannian_distance_finite_approximation (R : realType) n A g x y (r e : R) :
  @riemannian_distance R n A g x y = r%:E -> 0 < e ->
  exists C a b, is_riemannian_admissible_curve A x y C a b /\
    (riemannian_curve_cost g C a b < (r+e)%:E)%E.
Proof.
move=> hValue he; apply: contrapT=> hNo.
have hLower C a b : is_riemannian_admissible_curve A x y C a b ->
    ((r+e)%:E <= riemannian_curve_cost g C a b)%E.
  move=> hC; rewrite leNgt; apply/negP=> hBad.
  apply: hNo; exists C,a,b; by split.
have h := riemannian_distance_greatest (riemannian_distance_laws A g x y) hLower.
rewrite hValue lee_fin in h.
have hRise : r < r+e by rewrite ltrDl.
by have hBad := lt_le_trans hRise h; rewrite ltxx in hBad.
Qed.
