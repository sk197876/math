(** Federer (1969), 3.4.8(6), p. 329:
    orthogonal coordinate changes compose on the
    original analytic germs. The actual representative
    equations prove the contravariant composition law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_analytic_pullback_composes]: actual
    germ pullback reverses composition, supporting
    I_(gh)=(I_g)_h in 3.4.8(6), p. 329.
    Every representative retains its actual values. *)
Theorem pointed_analytic_pullback_composes (R:realType) (X Y Z:lmodType R)
  (NX:X->R) (NY:Y->R) (NZ:Z->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
  (a:X) (b:Y) (c:Z) (u:X->Y) (v:Y->Z)
  (P:analytic_germ_space hNY b->analytic_germ_space hNX a)
  (Q:analytic_germ_space hNZ c->analytic_germ_space hNY b):
  is_pointed_analytic_germ_pullback u P ->is_pointed_analytic_germ_pullback v Q ->
  is_pointed_analytic_germ_pullback (fun x=>v (u x)) (fun alpha=>P (Q alpha)).
Proof.
move=>hP hQ f.
have [g [hG hValuesG]]:=hQ f.
have [h [hH hValuesH]]:=hP g.
exists h;split;first by rewrite hG hH.
move=>x;by rewrite hValuesH hValuesG.
Qed.

(** Source for [pointed_analytic_pullback_map_extensional]:
    equal actual coordinate maps have equal germ
    pullbacks, supporting the coordinate identities in
    3.4.8(6), p. 329. *)
Theorem pointed_analytic_pullback_map_extensional (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (a:X) (b:Y) (u v:X->Y)
  (P Q:analytic_germ_space hNY b->analytic_germ_space hNX a):
  is_pointed_analytic_germ_pullback u P ->is_pointed_analytic_germ_pullback v Q ->
  (forall x,u x = v x) ->forall alpha,P alpha = Q alpha.
Proof.
move=>hP hQ hEqual alpha.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY b alpha.
have [g [hG hValuesG]]:=hP f.
have [h [hH hValuesH]]:=hQ f.
rewrite hG hH;apply:analytic_germ_pointwise_equality=>x.
by rewrite hValuesG hValuesH hEqual.
Qed.
