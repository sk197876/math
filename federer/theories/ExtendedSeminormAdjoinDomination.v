(** Federer (1969), 2.4.12, p. 86: the real value chosen between the
    endpoints gives a dominated extension on the span with one additional
    vector. Infinite upper bounds are automatic; finite bounds reduce to the
    printed positive- and negative-coefficient argument. Source context:
    ExtendedSeminormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import PartialLinearMap LinearGraphAdjoinValue ExtendedSeminormUP ExtendedSeminormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Section Domination.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> \bar R.
Hypothesis hN : is_extended_seminorm N.
Variable G : V -> R^o -> Prop.
Hypothesis hG : linear_graph G.

(** Source for [extended_seminorm_adjoin_positive]: positive-
    coefficient case of the final extension formula in Federer
    2.4.12, p. 86. The upper-endpoint condition is
    needed only when its seminorm value is finite. *)
Lemma extended_seminorm_adjoin_positive v (a : R)
    (hu : forall x b, G x b -> N (x+v)%R \is a fin_num -> (a <= fine (N (x+v)%R)-b)%R)
    x b (c : R) : G x b -> (0<c)%R -> (b+c*a)%:E <= N (x+c *: v)%R.
Proof.
move=> hx hc; have hc0 : c != 0%R := lt0r_neq0 hc.
have [hfin|hfin] := boolP (N (x+c *: v)%R \is a fin_num).
- have he : (c^-1 *: (x+c *: v)=c^-1 *: x+v)%R.
    by rewrite scalerDr scalerA mulVf // scale1r.
  have hsmall : N (c^-1 *: x+v)%R \is a fin_num.
    rewrite (ge0_fin_numE (extended_seminorm_nonnegative hN _)) -he.
    apply: (@extended_seminorm_finite_scale R V N hN c^-1 (x+c *: v)%R).
    by move: hfin; rewrite (ge0_fin_numE (extended_seminorm_nonnegative hN _)).
  have hg := hG.2.2.1 (c^-1)%R _ _ hx.
  have h := hu _ _ hg hsmall.
  change (is_true (a <= fine (N (c^-1 *: x+v)%R)-c^-1*b)%R) in h.
  rewrite lerBrDl in h.
  have hm : (c * (c^-1*b+a) <= c*fine (N (c^-1 *: x+v)%R))%R.
    by rewrite (ler_pM2l hc).
  have hs := extended_seminorm_scale hN c (c^-1 *: x+v)%R.
  rewrite scalerDr scalerA mulfV // scale1r (ger0_norm (ltW hc)) -(fineK hsmall) -EFinM in hs.
  rewrite mulrDr mulrA mulfV // mul1r in hm.
  by rewrite hs lee_fin.
- have htop : N (x+c *: v)%R=+oo.
    move: hfin; rewrite (ge0_fin_numE (extended_seminorm_nonnegative hN _)) ltNge negbK.
    move=> h; apply/eqP; rewrite eq_le leey andTb; exact h.
  by rewrite htop leey.
Qed.

(** Source for [extended_seminorm_adjoin_coefficients]: all
    real coefficients in the extension formula of Federer
    2.4.12, p. 86. Negation interchanges the two
    interval conditions and zero uses the original domination. *)
Lemma extended_seminorm_adjoin_coefficients v (a : R)
    (hdom : forall x b, G x b -> b%:E <= N x)
    (hl : forall x b, G x b -> N (x-v)%R \is a fin_num -> (b-fine (N (x-v)%R) <= a)%R)
    (hu : forall x b, G x b -> N (x+v)%R \is a fin_num -> (a <= fine (N (x+v)%R)-b)%R)
    x b (c : R) : G x b -> (b+c*a)%:E <= N (x+c *: v)%R.
Proof.
move=> hx; case: (ltgtP c 0%R)=> [hc|hc|->].
- have hu' y d : G y d -> N (y+ -v)%R \is a fin_num -> (-a <= fine (N (y+ -v)%R)-d)%R.
    move=> hy hfin; rewrite lerNl opprB; exact: hl hy hfin.
  have hc' : (0 < -c)%R by rewrite oppr_gt0.
  have h := @extended_seminorm_adjoin_positive (-v)%R (-a)%R hu' x b (-c)%R hx hc'.
  by rewrite mulrNN scalerN scaleNr opprK in h.
- exact: (@extended_seminorm_adjoin_positive v a hu x b c hx hc).
- rewrite mul0r addr0 scale0r addr0; exact: hdom hx.
Qed.

(** Source for [extended_seminorm_adjoin_graph_dominated]:
    complete domination of the single-vector graph extension in
    Federer 2.4.12, p. 86, for extended-valued seminorms. *)
Theorem extended_seminorm_adjoin_graph_dominated v (a : R)
    (hdom : forall x b, G x b -> b%:E <= N x)
    (hl : forall x b, G x b -> N (x-v)%R \is a fin_num -> (b-fine (N (x-v)%R) <= a)%R)
    (hu : forall x b, G x b -> N (x+v)%R \is a fin_num -> (a <= fine (N (x+v)%R)-b)%R)
    x b : graph_adjoin_value G v a x b -> b%:E <= N x.
Proof.
move=> [c hc].
have h := @extended_seminorm_adjoin_coefficients v a hdom hl hu
  (x-c *: v)%R (b-c*a)%R c hc.
by rewrite !subrK in h.
Qed.
End Domination.
