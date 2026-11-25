(** Supporting calculus for Federer (1969), 3.1.1, pp. 210–211:
    sums and scalar multiples of the linear approximations. These laws
    support the coordinate and partial-derivative formulas. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_add]: supporting sum rule for the
    linear calculus used in Federer 3.1.1, pp. 210–211. Both functions
    have the specified common domain; their differentials add. *)
Theorem norm_differential_add (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNY : is_real_norm NY)
    (A : X -> Prop) (f g : X -> Y) (a : X) (L M : Hom X Y) :
  has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY A g a M ->
  has_norm_differential NX NY A (fun x => f x+g x) a (L+M).
Proof.
move=> hf hg; split; first exact: norm_differential_interior hf.
- exact: (@norm_bounded_linear_add R X Y NX NY hNY L M
    (norm_differential_bounded hf) (norm_differential_bounded hg)).
- move=> e he.
  have hp : 0 < e/2 by rewrite divr_gt0 // ltr0n.
  have [r [hr hrf]] := norm_differential_remainder hf hp.
  have [s [hs hrg]] := norm_differential_remainder hg hp.
  exists (Num.min r s); split; first by rewrite lt_min hr hs.
  move=> h ha hh.
  have hmr : Num.min r s <= r by rewrite ge_min lexx.
  have hms : Num.min r s <= s by rewrite ge_min lexx orbT.
  have hfr := hrf h ha (lt_le_trans hh hmr).
  have hgr := hrg h ha (lt_le_trans hh hms).
  have heq : (f (a+h)+g (a+h))-(f a+g a)-(L+M) h =
      (f (a+h)-f a-L h)+(g (a+h)-g a-M h).
    by rewrite hom_addE !opprD
      (addrACA (f (a+h)) (g (a+h)) (-f a) (-g a))
      (addrACA (f (a+h)-f a) (g (a+h)-g a) (-L h) (-M h)).
  rewrite heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  apply: le_trans (lerD hfr hgr) _.
  have heq2 : e/2+e/2=e by lra.
  by rewrite -mulrDl heq2.
Qed.

(** Source for [norm_differential_scale]: supporting scalar rule for
    the linear combinations in Federer 3.1.1, pp. 210–211. The zero
    coefficient is included without division by its absolute value. *)
Theorem norm_differential_scale (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) (c : R) :
  has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY A (fun x => c *: f x) a (c *: L).
Proof.
move=> hf; split; first exact: norm_differential_interior hf.
- exact: (@norm_bounded_linear_scale R X Y NX NY hNY L c
    (norm_differential_bounded hf)).
- move=> e he.
  have hn : 0 < `|c|+1 by have := normr_ge0 c; lra.
  have hp : 0 < e/(`|c|+1) by rewrite divr_gt0.
  have [d [hd hrf]] := norm_differential_remainder hf hp.
  exists d; split=> // h ha hh.
  rewrite hom_scaleE -!scalerBr (real_seminorm_scale hNY.1).
  apply: le_trans (ler_wpM2l (normr_ge0 c) (hrf h ha hh)) _.
  rewrite mulrA; apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNX.1 h.
  have hb : `|c|*(e/(`|c|+1)) <= (`|c|+1)*(e/(`|c|+1)).
    apply: ler_wpM2r; first exact: ltW hp.
    by rewrite lerDl.
  apply: le_trans hb _.
  by rewrite mulrC divfK // gt_eqF.
Qed.
