(** Federer (1969), 2.4.12, p. 86, Hahn–Banach proof: compare the lower and
    upper endpoints when adjoining one vector. We retain infinite seminorm
    values. The real interval is nonempty even when every printed lower
    endpoint is minus infinity: then every upper endpoint is infinity, and
    zero is admissible. Source context: ExtendedSeminormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialLinearMap ExtendedSeminormUP ExtendedSeminormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Interval.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> \bar R.
Hypothesis hN : is_extended_seminorm N.
Variable G : V -> R^o -> Prop.
Hypothesis hG : linear_graph G.
Hypothesis hdom : forall x c, G x c -> c%:E <= N x.
Variable v : V.

(** Source for [extended_seminorm_finite_endpoints_ordered]:
    the displayed interval inequality in Federer 2.4.12,
    p. 86, for the finite endpoints. Infinite endpoints
    impose no constraint on a real candidate value. *)
Lemma extended_seminorm_finite_endpoints_ordered x y c d :
  G x c -> G y d -> N (x-v)%R \is a fin_num -> N (y+v)%R \is a fin_num ->
  (c-fine (N (x-v)%R) <= fine (N (y+v)%R)-d)%R.
Proof.
move=> hx hy hl hu.
have hxy : G (x+y)%R (c+d)%R := hG.2.1 _ _ _ _ hx hy.
have he : ((x-v)+(y+v)=x+y)%R by rewrite addrACA addNr addr0.
have ht := extended_seminorm_triangle hN (x-v)%R (y+v)%R.
rewrite he in ht.
have h := le_trans (hdom hxy) ht.
rewrite -(fineK hl) -(fineK hu) -EFinD lee_fin in h.
rewrite lerBrDr addrAC lerBlDl; exact h.
Qed.

(** Source for [extended_seminorm_real_lower_endpoints]:
    the finite members of the lower-endpoint set in Federer
    2.4.12, p. 86. Omitting minus infinity makes
    it possible to take a real supremum when this set is nonempty. *)
Definition extended_seminorm_real_lower_endpoints : set R :=
  fun r => exists x c, G x c /\ N (x-v)%R \is a fin_num /\
    r=(c-fine (N (x-v)%R))%R.

(** Source for [extended_seminorm_real_interval_exists]: the
    choice of a real c between the displayed endpoints in
    Federer 2.4.12, p. 86, with the degenerate
    infinite-endpoint case made explicit. This is an existence
    proof, not an additional extension axiom. *)
Theorem extended_seminorm_real_interval_exists : exists a : R,
  (forall x c, G x c -> N (x-v)%R \is a fin_num -> (c-fine (N (x-v)%R) <= a)%R) /\
  (forall y d, G y d -> N (y+v)%R \is a fin_num -> (a <= fine (N (y+v)%R)-d)%R).
Proof.
have [hn|hn] := pselect (exists r, extended_seminorm_real_lower_endpoints r).
- have [r [x [c [hx [hfin hr]]]]] := hn.
  have hneg : G (-x)%R (-c)%R.
    have h := hG.2.2.1 (-1)%R _ _ hx.
    by rewrite !scaleN1r in h.
  have hsym : N (-x+v)%R=N (x-v)%R.
    by rewrite addrC -opprB (extended_seminorm_negate hN).
  have hupper : ubound extended_seminorm_real_lower_endpoints (fine (N (-x+v)%R)+c)%R.
    move=> s [y [d [hy [hyfin ->]]]].
    have hh := @extended_seminorm_finite_endpoints_ordered y (-x)%R d (-c)%R hy hneg hyfin.
    rewrite opprK in hh; apply: hh; by rewrite hsym.
  exists (sup extended_seminorm_real_lower_endpoints); split.
  + move=> y d hy hyfin; apply: ub_le_sup; first by exists (fine (N (-x+v)%R)+c)%R.
    exists y,d; by split=> //; split.
  + move=> y d hy hyfin; apply: ge_sup=> // s [z [e [hz [hzfin ->]]]].
    exact: extended_seminorm_finite_endpoints_ordered hz hy hzfin hyfin.
- exists 0%R; split.
  + move=> x c hx hfin; exfalso; apply: hn.
    exists (c-fine (N (x-v)%R))%R; exists x,c; by split=> //; split.
  + move=> y d hy hfin; exfalso; apply: hn.
    exists (-d-fine (N (-y-v)%R))%R; exists (-y)%R,(-d)%R; split.
    * have h := hG.2.2.1 (-1)%R _ _ hy; by rewrite !scaleN1r in h.
    * split=> //; by rewrite -opprD (extended_seminorm_negate hN).
Qed.
End Interval.
