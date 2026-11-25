(** Federer (1969), 3.1.11, p. 222: continuity and linear
    growth along a fixed source line, used in the composition of jets. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  NormTaylorLineValues NormClassOneLocalLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_line_small]: small scalar increments
    stay in the domain and have small image increments, supporting
    the composition-of-jets limit in Federer 3.1.11, p. 222.
    The direction is arbitrary, including zero. *)
Lemma norm_class_zero_line_small (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (A : X->Prop) (f : X->Y) a v :
  A a -> norm_class_zero NX NY A f ->
  forall e : R, 0<e -> exists d : R, 0<d /\ forall t,
    `|t|<d -> A (a+t*:v) /\ NY (f (a+t*:v)-f a)<e.
Proof.
move=>ha hf e he.
have [r [hr hA]] := (hf a ha).1.
have [s [hs hc]] := (hf a ha).2 e he.
have hmin : 0<Num.min r s by rewrite lt_min hr hs.
have [d [hd hb]] := norm_scalar_line_small_increments hNX v hmin.
exists d; split=> // t ht.
have hh := hb t ht.
have /andP [hhr hhs] : (NX (t*:v)<r)&&(NX (t*:v)<s) by rewrite -lt_min.
have hav := hA (t*:v) hhr.
split; first exact hav; exact (hc (t*:v) hav hhs).
Qed.

(** Source for [norm_class_one_line_growth]: the increment
    f(a+t v)-f(a) is O(|t|), supporting the substitution into
    the outer Taylor remainder in Federer 3.1.11, p. 222.
    This follows from the proved local Lipschitz bound. *)
Lemma norm_class_one_line_growth (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) a v :
  A a -> norm_class_one NX NY A f ->
  exists C r : R, 0<=C /\ 0<r /\ forall t,
    `|t|<r -> A (a+t*:v) /\ NY (f (a+t*:v)-f a)<=C*`|t|.
Proof.
move=>ha hf.
have [C [d [hC [hd [hA hLip]]]]] := norm_class_one_local_lipschitz hNX hNY ha hf.
have [r [hr hb]] := norm_scalar_line_small_increments hNX v hd.
exists (C*NX v), r; split.
- exact (mulr_ge0 (ltW hC) (real_seminorm_nonnegative hNX.1 v)).
split; first exact hr.
move=>t ht.
have he : a+t*:v-a=t*:v by rewrite addrAC subrr add0r.
have hsmall : NX (a+t*:v-a)<d by rewrite he; exact: hb t ht.
split; first exact: hA _ hsmall.
have ha0 : NX (a-a)<d by rewrite subrr (real_seminorm_zero hNX.1).
have hh := hLip (a+t*:v) a hsmall ha0.
by rewrite he (real_seminorm_scale hNX.1) mulrA mulrAC in hh.
Qed.
