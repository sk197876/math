(** Federer (1969), 1.10.5, p. 48: supporting normed extension step for the
    dual representation. The proof follows 2.4.12, p. 86: a value between
    the lower and upper endpoints preserves domination on the span of the
    old domain and one new vector. Only finite-valued seminorms are used. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RealNormUP PartialLinearMap LinearGraphAdjoinValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Domination.
Variable R : realFieldType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variable G : V -> R^o -> Prop.
Hypothesis hG : linear_graph G.

(** Source for [seminorm_adjoin_positive_coefficient]: Federer
    1.10.5, p. 48, supporting positive-coefficient case of the
    extension in 2.4.12, p. 86. The upper endpoint inequality,
    applied after dividing by c>0, bounds f(x)+c*a by N(x+c*v). *)
Lemma seminorm_adjoin_positive_coefficient v a
    (hu : forall x b, G x b -> a <= N(x+v)-b) x b c :
  G x b -> 0<c -> b+c*a <= N(x+c *: v).
Proof.
move=> hx hc.
have hcx : c!=0 := lt0r_neq0 hc.
have hg := (proj1 (proj2 (proj2 hG))) c^-1 _ _ hx.
have h := hu _ _ hg.
change (is_true (a <= N(c^-1 *: x+v)-c^-1*b)) in h.
rewrite lerBrDl in h.
have hm : c * (c^-1*b+a) <= c * N(c^-1 *: x+v).
  by rewrite (ler_pM2l hc).
have hs := real_seminorm_scale hN c (c^-1 *: x+v).
rewrite scalerDr scalerA (mulfV hcx) scale1r (ger0_norm (ltW hc)) in hs.
rewrite mulrDr mulrA (mulfV hcx) mul1r -hs in hm.
exact: hm.
Qed.

(** Source for [seminorm_adjoin_all_coefficients]: Federer
    1.10.5, p. 48, supporting extension inequality for every
    real coefficient. Negative coefficients use the lower endpoint,
    and zero coefficients use the original domination. *)
Lemma seminorm_adjoin_all_coefficients v a
    (hdom : forall x b, G x b -> b<=N x)
    (hl : forall x b, G x b -> b-N(x-v)<=a)
    (hu : forall x b, G x b -> a<=N(x+v)-b) x b c :
  G x b -> b+c*a <= N(x+c *: v).
Proof.
move=> hx; case: (ltgtP c 0)=> [hc|hc|->].
- have hu' y d : G y d -> -a<=N(y + -v)-d.
    move=> hy; rewrite lerNl opprB; exact: hl.
  have hc' : 0 < -c by rewrite oppr_gt0.
  have h := @seminorm_adjoin_positive_coefficient (-v) (-a) hu' x b (-c) hx hc'.
  by rewrite mulrNN scalerN scaleNr opprK in h.
- exact: (@seminorm_adjoin_positive_coefficient v a hu x b c hx hc).
- rewrite mul0r addr0 scale0r addr0; exact: hdom.
Qed.

(** Source for [seminorm_adjoin_graph_dominated]: Federer
    1.10.5, p. 48, the complete single-vector step from
    2.4.12, p. 86. Every pair in the extended graph obeys
    the same seminorm bound when the prescribed value lies in the interval. *)
Theorem seminorm_adjoin_graph_dominated v a
    (hdom : forall x b, G x b -> b<=N x)
    (hl : forall x b, G x b -> b-N(x-v)<=a)
    (hu : forall x b, G x b -> a<=N(x+v)-b) x b :
  graph_adjoin_value G v a x b -> b<=N x.
Proof.
move=> [c hc].
have h := @seminorm_adjoin_all_coefficients v a hdom hl hu
  (x-c *: v) (b-c*a) c hc.
by rewrite !subrK in h.
Qed.
End Domination.
