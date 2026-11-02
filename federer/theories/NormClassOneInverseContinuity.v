(** Federer (1969), 3.1.1, p. 210: a univalent class-one map with
    invertible differentials has a continuous inverse on an open image.
    Completeness is the hypothesis retained from the preceding
    inverse-function argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  NormDifferentialUP NormClassOneUP NormClassOneInverseBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_inverse_class_zero]: supporting
    first part of the class-one inverse assertion in Federer 3.1.1,
    p. 210. The image domain is open and the inverse is continuous.
    The explicit inverse laws specify a univalent map onto that domain;
    continuity of the inverse is proved from the local ball theorem. *)
Theorem norm_class_one_inverse_class_zero (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
    (A : X -> Prop) (B : Y -> Prop) (f : X -> Y) (g : Y -> X)
    (D : X -> Hom X Y) (E : X -> Hom Y X) :
  is_norm_class_one_field NX NY A f D ->
  (forall x, A x -> norm_bounded_linear NY NX (E x)) ->
  (forall x, A x -> forall v, E x (D x v)=v) ->
  (forall x, A x -> forall w, D x (E x w)=w) ->
  (forall x, A x -> B (f x) /\ g (f x)=x) ->
  (forall y, B y -> A (g y) /\ f (g y)=y) ->
  norm_class_zero NY NX B g.
Proof.
move=> hf hE hED hDE hgf hfg b hb.
pose a := g b.
have ha : A a := (hfg b hb).1.
have hfa : f a=b := (hfg b hb).2.
have [r [s [K [hr [hs [hK [hAr [hbound [hinj honto]]]]]]]]] :=
  @norm_class_one_inverse_ball R X Y NX NY hNX hNY hcomplete A f D a (E a)
    hf ha (hE a ha) (hED a ha) (hDE a ha).
have haBall : NX (a-a) <= r.
  rewrite subrr (real_seminorm_zero hNX.1); exact: ltW hr.
have hlocal : forall k, NY k <= s -> NX (g (b+k)-a) <= K*NY k.
  move=> k hk.
  have hy : NY ((b+k)-f a) <= s by rewrite hfa addrAC subrr add0r.
  have [x [hx hfx]] := honto (b+k) hy.
  have hgx : g (b+k)=x by rewrite -hfx; exact: (hgf x (hAr x hx)).2.
  have hh := hbound x a hx haBall.
  by rewrite hgx hfx hfa addrAC subrr add0r in hh *.
split.
- exists s; split=> // k hk.
  have hy : NY ((b+k)-f a) <= s by rewrite hfa addrAC subrr add0r; exact: ltW hk.
  have [x [hx hfx]] := honto (b+k) hy.
  rewrite -hfx; exact: (hgf x (hAr x hx)).1.
- move=> e he.
  have hK1 : 0 < K+1 by lra.
  have hd : 0 < e/(K+1) by rewrite divr_gt0.
  exists (Num.min s (e/(K+1))); split; first by rewrite lt_min hs hd.
  move=> k _ hk.
  have hks : NY k <= s.
    apply: ltW; apply: lt_le_trans hk _; by rewrite ge_min lexx.
  have hke : NY k < e/(K+1).
    apply: lt_le_trans hk _; by rewrite ge_min lexx orbT.
  apply: le_lt_trans (hlocal k hks) _.
  have hn := real_seminorm_nonnegative hNY.1 k.
  have hh : (K+1)*NY k < e by move: hke; rewrite ltr_pdivlMr // mulrC.
  by nra.
Qed.
