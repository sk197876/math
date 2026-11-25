(** Federer (1969), 2.9.22, p. 167: every continuous dual scalarisation of a
    locally BV normed curve is locally BV. This module proves the metric
    Lipschitz postcomposition estimate from the original partition supremum
    of 2.5.16, p. 109. No completeness or reflexivity is needed for this
    supporting fact. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import CurveVariationUP CurveArcLength ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_lipschitz_curve_chain_bound]: supporting
    scalarisation estimate in Federer 2.9.22, p. 167, from the
    partition sums of 2.5.16, p. 109. A map with constant L
    increases any finite chain length by at most L. This statement
    includes repeated points and empty chains. *)
Lemma metric_lipschitz_curve_chain_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (g : R -> X) (L : R) : 0<=L ->
  (forall x y, mdist (f x) (f y)<=L*mdist x y) ->
  forall s, chain_sum (fun t => f (g t)) s<=L*chain_sum g s.
Proof.
move=> hL hf; elim=> [|a [|b rest] ih]; first by rewrite /= mulr0.
- by rewrite /= mulr0.
- rewrite !chain_sum_cons mulrDr.
  exact: lerD (hf _ _) (ih).
Qed.

(** Source for [metric_lipschitz_curve_variation_bound]: supporting
    local variation bound for Federer 2.9.22, p. 167. On a
    finite-variation segment, each postcomposition partition sum is
    at most L times the original variation. The bound uses the
    proved finite representative, so L=0 causes no infinite product. *)
Lemma metric_lipschitz_curve_variation_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (g : R -> X) (L a b : R) : 0<=L ->
  (forall x y, mdist (f x) (f y)<=L*mdist x y) ->
  curve_locally_finite_variation g -> a<=b ->
  (curve_variation (fun t => f (g t)) a b<=(L*fine (curve_variation g a b))%:E)%E.
Proof.
move=> hL hf hg hab.
have hfin := @curve_variation_fin_num R X g hg a b hab.
apply: extended_real_sup_least=> z [s [hs ->]].
have hchain := metric_lipschitz_curve_chain_bound g hL hf s.
have hupper : ((chain_sum g s)%:E<=curve_variation g a b)%E.
  apply: extended_real_sup_upper; by exists s.
have hreal : chain_sum g s<=fine (curve_variation g a b).
  by move: hupper; rewrite -(fineK hfin) lee_fin.
rewrite lee_fin; exact: le_trans hchain (ler_wpM2l hL hreal).
Qed.

(** Source for [metric_lipschitz_curve_locally_finite_variation]:
    supporting locally BV hypothesis for scalar evaluations in Federer
    2.9.22, p. 167. A Lipschitz map sends every locally BV metric
    curve to a locally BV curve, including a zero Lipschitz bound. *)
Lemma metric_lipschitz_curve_locally_finite_variation (R : realType) (X Y : metricType R)
    (f : X -> Y) (g : R -> X) (L : R) : 0<=L ->
  (forall x y, mdist (f x) (f y)<=L*mdist x y) ->
  curve_locally_finite_variation g -> curve_locally_finite_variation (fun t => f (g t)).
Proof.
move=> hL hf hg a b hab.
exact: le_lt_trans (@metric_lipschitz_curve_variation_bound R X Y f g L a b hL hf hg hab) (ltry _).
Qed.
