(** Uniqueness of the finite limits specified for Federer (1969),
    3.1.1, p. 209. Eventual estimates and arbitrarily close witnesses
    determine each limit; no chosen sequence is part of the interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import NormRatioLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_ratio_limsup_unique]: uniqueness of the upper
    limit in Federer 3.1.1, p. 209, from its epsilon sharpness laws. *)
Lemma norm_ratio_limsup_unique (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y)
    (a : X) (l m : R) :
  is_norm_ratio_limsup NX NY A f a l ->
  is_norm_ratio_limsup NX NY A f a m -> l = m.
Proof.
have hle : forall u v : R,
    is_norm_ratio_limsup NX NY A f a u ->
    is_norm_ratio_limsup NX NY A f a v -> u <= v.
  move=> u v hu hv; case: (leP u v)=> // hlt.
  have he : 0 < (u-v)/3 by lra.
  have [d [hd hb]] := norm_ratio_eventual_upper hv he.
  have [h [ha [hh hq]]] := norm_ratio_sharp_upper hu he hd.
  have hq' := hb h ha hh; exfalso; by lra.
move=> hl hm; apply/eqP; by rewrite eq_le (hle _ _ hl hm) (hle _ _ hm hl).
Qed.

(** Source for [norm_ratio_liminf_unique]: uniqueness of the lower
    limit in Federer 3.1.1, p. 209, from its epsilon sharpness laws. *)
Lemma norm_ratio_liminf_unique (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y)
    (a : X) (l m : R) :
  is_norm_ratio_liminf NX NY A f a l ->
  is_norm_ratio_liminf NX NY A f a m -> l = m.
Proof.
have hle : forall u v : R,
    is_norm_ratio_liminf NX NY A f a u ->
    is_norm_ratio_liminf NX NY A f a v -> u <= v.
  move=> u v hu hv; case: (leP u v)=> // hlt.
  have he : 0 < (u-v)/3 by lra.
  have [d [hd hb]] := norm_ratio_eventual_lower hu he.
  have [h [ha [hh hq]]] := norm_ratio_sharp_lower hv he hd.
  have hq' := hb h ha hh; exfalso; by lra.
move=> hl hm; apply/eqP; by rewrite eq_le (hle _ _ hl hm) (hle _ _ hm hl).
Qed.
