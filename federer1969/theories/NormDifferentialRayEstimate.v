(** Federer (1969), 3.1.1, p. 209: approach the point along a unit
    direction to obtain sharp local increment-ratio bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRatioLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_ray_estimate]: supporting ray estimate
    for the limsup and liminf identities in Federer 3.1.1, p. 209.
    Along a unit direction v, the increment ratio tends to the length
    of L(v). Domain membership follows from the interior hypothesis. *)
Lemma norm_differential_ray_estimate (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) :
  has_norm_differential NX NY A f a L -> forall v, NX v = 1 ->
  forall e : R, 0 < e -> exists d : R, 0 < d /\ forall t : R,
    0 < t < d -> A (a+t *: v) /\ NX (t *: v) = t /\
    `|norm_increment_ratio NX NY f a (t *: v)-NY (L v)| <= e.
Proof.
move=> hf v hv e he.
have [r [hr hA]] := norm_differential_interior hf.
have [s [hs hrem]] := norm_differential_remainder hf he.
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=> t /andP [ht hts].
have hmr : Num.min r s <= r by rewrite ge_min lexx.
have hms : Num.min r s <= s by rewrite ge_min lexx orbT.
have hnorm : NX (t *: v) = t.
  by rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)) hv mulr1.
have ha : A (a+t *: v) by apply: hA; rewrite hnorm; exact: lt_le_trans hts hmr.
split=> //; split=> //.
have hsmall : NX (t *: v) < s by rewrite hnorm; exact: lt_le_trans hts hms.
have hb := hrem _ ha hsmall; rewrite hnorm in hb.
pose k := f (a+t *: v)-f a.
have hl : NY (L (t *: v)) = t*NY (L v).
  by rewrite linearZ /= (real_seminorm_scale hNY.1) (ger0_norm (ltW ht)).
have hu : NY k <= t*NY (L v)+e*t.
  have hEq : k = L (t *: v)+(k-L (t *: v)) by rewrite addrC subrK.
  rewrite {1}hEq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  rewrite hl; exact: lerD (lexx _) hb.
have hd : t*NY (L v) <= NY k+e*t.
  have hEq : L (t *: v) = k + -(k-L (t *: v)) by rewrite opprB addrC subrK.
  rewrite -hl {1}hEq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  rewrite (real_seminorm_negate hNY.1); exact: lerD (lexx _) hb.
pose q := norm_increment_ratio NX NY f a (t *: v).
have hq : q*t = NY k by rewrite /q /norm_increment_ratio hnorm divfK // gt_eqF.
change (`|q-NY (L v)| <= e); rewrite ler_norml; apply/andP; split; by nra.
Qed.

(** Source for [norm_differential_unit_probe]: sharpness step for the
    limits in Federer 3.1.1, p. 209. Every unit-direction image length
    is approximated by an increment ratio inside any prescribed positive
    radius, while remaining in the function's actual domain. *)
Lemma norm_differential_unit_probe (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) :
  has_norm_differential NX NY A f a L -> forall v, NX v = 1 ->
  forall e d : R, 0 < e -> 0 < d -> exists h,
    A (a+h) /\ 0 < NX h < d /\
    `|norm_increment_ratio NX NY f a h-NY (L v)| <= e.
Proof.
move=> hf v hv e d he hd.
have [r [hr hb]] := @norm_differential_ray_estimate R X Y NX NY hNX hNY A f a L hf v hv e he.
pose t := Num.min r d / 2.
have hmin : 0 < Num.min r d by rewrite lt_min hr hd.
have ht : 0 < t by rewrite /t divr_gt0 // ltr0n.
have hhalf : t < Num.min r d by rewrite /t; lra.
have hmr : Num.min r d <= r by rewrite ge_min lexx.
have hmd : Num.min r d <= d by rewrite ge_min lexx orbT.
have htr : 0 < t < r by apply/andP; split=> //; exact: lt_le_trans hhalf hmr.
have [ha [hn heq]] := hb t htr.
exists (t *: v); split=> //; split=> //.
rewrite hn; apply/andP; split=> //; exact: lt_le_trans hhalf hmd.
Qed.
