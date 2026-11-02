(** Federer (1969), 2.9.22, p. 167: the Lipschitz case of the locally
    finite-variation hypothesis. These supporting estimates derive
    V_a^b(g)<=L(b-a) from the partition definition in 2.5.16, p. 109. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import CurveVariationUP CurveArcLength ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_curve_chain_sum_bound]: supporting
    finite-partition estimate for the Lipschitz case of Federer
    2.9.22, p. 167, using 2.5.16, p. 109.
    The ordered interval widths telescope, including zero widths. *)
Lemma lipschitz_curve_chain_sum_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (L : R) :
  (forall t u, mdist (g t) (g u)<=L * `|t-u|) ->
  forall s : seq R, sorted <=%O s ->
    chain_sum g s<=L * (last 0 s-head 0 s).
Proof.
move=> hL; elim=> [|t [|u rest] ih].
- by move=> _; rewrite /= subrr mulr0.
- by move=> _; rewrite /= subrr mulr0.
move=> hs.
have /andP [htu hrest] : (t<=u) && sorted <=%O (u::rest) by exact hs.
have ht := ih hrest.
have hd := hL t u.
have htu0 : t-u<=0 by rewrite subr_le0.
rewrite (ler0_norm htu0) opprB in hd.
rewrite chain_sum_cons.
change (mdist (g t) (g u)+chain_sum g (u::rest)<=L * (last 0 (u::rest)-t)).
have he : L * (last 0 (u::rest)-t) = L * (u-t)+L * (last 0 (u::rest)-u) by ring.
rewrite he; exact: lerD hd ht.
Qed.

(** Source for [lipschitz_curve_variation_bound]: supporting
    variation bound in the Lipschitz case of Federer 2.9.22,
    p. 167, from the supremum in 2.5.16, p. 109.
    This applies to any metric target, without completeness. *)
Lemma lipschitz_curve_variation_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (L a b : R) :
  (forall t u, mdist (g t) (g u)<=L * `|t-u|) ->
  (curve_variation g a b<=(L * (b-a))%:E)%E.
Proof.
move=> hL; apply: extended_real_sup_least=> z [s [[hs [hsize [hhead hlast]]] ->]].
rewrite lee_fin.
have hb := lipschitz_curve_chain_sum_bound hL hs.
have hhead0 : head 0 s = a.
  case E: s=> [|t rest]; first by move: hsize; rewrite E.
  by move: hhead; rewrite E.
have hlast0 : last 0 s = b.
  case E: s=> [|t rest]; first by move: hsize; rewrite E.
  by move: hlast; rewrite E.
by rewrite hhead0 hlast0 in hb.
Qed.

(** Source for [lipschitz_curve_locally_finite_variation]:
    applicability of the BV derivative theorem to Lipschitz
    scalarisations in Federer 2.9.22, p. 167. The finite
    Lipschitz estimate proves the hypothesis; it is not added
    as an independent assumption. *)
Lemma lipschitz_curve_locally_finite_variation (R : realType) (Y : metricType R)
    (g : R -> Y) (L : R) :
  (forall t u, mdist (g t) (g u)<=L * `|t-u|) ->
  curve_locally_finite_variation g.
Proof.
move=> hL a b _.
exact: le_lt_trans (lipschitz_curve_variation_bound a b hL) (ltry _).
Qed.
