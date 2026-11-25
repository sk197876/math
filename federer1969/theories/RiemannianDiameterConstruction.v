(** Existence proof only for the independently specified
    original rho diameter, Federer (1969), 3.2.46, p. 281.
    Later proofs use the sealed order interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier RiemannianDistance
  ExtendedRealBounds RiemannianDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_diameter_exists]: the supremum
    exists also for empty sets and disconnected charts,
    supporting the actual Hausdorff measures in 3.2.46, p. 281. *)
Lemma riemannian_diameter_exists (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (S : set (riemannian_metric_space hg)) :
  exists d, @is_riemannian_diameter R n A g hg S d.
Proof.
pose D := [set r : \bar R | r=0 \/ exists x y,
  S x /\ S y /\ r=@riemannian_distance R n A g (val x) (val y)].
exists (extended_real_sup D); constructor.
- apply: extended_real_sup_upper; by left.
- move=> x y hx hy; apply: extended_real_sup_upper.
  right; exists x,y; by split=> //; split.
- move=> b hb hBound; apply: extended_real_sup_least.
  move=> r [->|[x [y [hx [hy ->]]]]]; first exact hb.
  exact: hBound x y hx hy.
Qed.
