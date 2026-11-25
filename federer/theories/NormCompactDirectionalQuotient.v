(** Federer (1969), 4.1.1, p. 346: compact-
    uniform directional difference quotients follow
    from the original first Taylor remainder.
    This supporting estimate retains the zero
    direction and every compact source set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormFirstTaylorCompactRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_compact_directional_quotient]: uniformly
    over a compact K, the directional quotient
    approaches the actual directional differential,
    supporting Federer 4.1.1, p. 346. *)
Theorem norm_compact_directional_quotient (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U K:X->Prop) (f:X->Y):
  norm_class hNX hNY U f 1%N ->
  compact [set x:real_norm_metric_space hNX|K x] ->(K `<=` U) ->
  forall v:X,forall e:R,0<e ->exists d:R,0<d /\ forall a,
    K a ->forall t,0<`|t|<d ->forall L:Hom X Y,
      has_norm_differential NX NY U f a L ->
      NY (t^-1*:(f (a+t*:v)-f a)-L v)<e.
Proof.
move=>hClass hK hKU v e he.
have hn := real_seminorm_nonnegative hNX.1 v.
have hn1 : 0 < NX v+1 by lra.
have he' : 0 < e/(NX v+1) by rewrite divr_gt0.
have [d [hd hrem]]:=@norm_first_taylor_compact_remainder R X Y NX NY hNX hNY U K f hClass hK hKU
  (e/(NX v+1)) he'.
exists (d/(NX v+1)); split; first by rewrite divr_gt0.
move=> a ha t /andP [ht hsmall] L hL.
have ht0 : t != 0 by move: ht; rewrite normr_gt0.
have htN : `|t| * (NX v+1) < d.
  by move: hsmall; rewrite ltr_pdivlMr.
have hinc : NX (t *: v) < d.
  rewrite (real_seminorm_scale hNX.1).
  apply: le_lt_trans _ htN.
  by rewrite ler_wpM2l // lerDl.
have hb:=hrem a (t*:v) ha hinc L hL.
have heq : t^-1 *: (f (a+t *: v)-f a)-L v =
    t^-1 *: (f (a+t *: v)-f a-L (t *: v)).
  by rewrite [RHS]scalerBr [L (_ *: _)]linearZ /= scalerA mulVf // scale1r.
rewrite heq (real_seminorm_scale hNY.1).
apply: le_lt_trans (ler_wpM2l (normr_ge0 _) hb) _.
rewrite (real_seminorm_scale hNX.1) normfV.
have hcancel : `|t|^-1 * (e/(NX v+1) * (`|t| * NX v)) =
    e/(NX v+1) * NX v.
  rewrite mulrCA; congr (_ * _).
  by rewrite mulrA mulVf ?mul1r // normr_eq0.
rewrite hcancel.
have hl : e/(NX v+1) * NX v < e/(NX v+1) * (NX v+1).
  by rewrite ltr_pM2l // ltrDl.
apply: lt_le_trans hl _.
by rewrite divfK ?lexx //; exact: lt0r_neq0 hn1.
Qed.
