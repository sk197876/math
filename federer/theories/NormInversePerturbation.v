(** Supporting continuity of inverse differentials in Federer (1969),
    3.1.1, p. 210: the inverse of a univalent class-one map is class one.
    All estimates are derived from inverse identities and norm bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_inverse_perturbation_bound]: supporting uniform
    bound for nearby inverse differentials in Federer 3.1.1, p. 210.
    If M0 is bounded by C and L differs from L0 by at most d, with
    2Cd at most one, then any inverse M of L is bounded by 2C. *)
Lemma norm_inverse_perturbation_bound (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L0 L : Hom X Y) (M0 M : Hom Y X)
    (C d : R) :
  0 < C -> 0 <= d -> 2*C*d <= 1 ->
  (forall v, M0 (L0 v)=v) -> (forall w, L (M w)=w) ->
  (forall w, NX (M0 w) <= C*NY w) ->
  (forall v, NY (L v-L0 v) <= d*NX v) ->
  forall w, NX (M w) <= 2*C*NY w.
Proof.
move=> hC hd hCd hM0L0 hLM hM0 hdiff w.
have heq : M w = M0 w+M0 (L0 (M w)-L (M w)).
  by rewrite linearB /= hM0L0 hLM addrC subrK.
have herr : NY (L0 (M w)-L (M w)) <= d*NX (M w).
  rewrite (real_seminorm_subtract hNY.1); exact: hdiff.
have hh := real_seminorm_triangle hNX.1 (M0 w) (M0 (L0 (M w)-L (M w))).
rewrite -heq in hh.
have hb := le_trans (hM0 (L0 (M w)-L (M w))) (ler_wpM2l (ltW hC) herr).
have ht := le_trans hh (lerD (hM0 w) hb).
have hn := real_seminorm_nonnegative hNX.1 (M w).
have he := ler_wpM2r hn hCd.
by nra.
Qed.

(** Source for [norm_inverse_difference_bound]: supporting
    continuity of inverse differentials in Federer 3.1.1, p. 210.
    The identity M-M0=M(L0-L)M0 turns a perturbation bound for L into
    a perturbation bound for its inverse. *)
Lemma norm_inverse_difference_bound (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNY : is_real_norm NY)
    (L0 L : Hom X Y) (M0 M : Hom Y X) (C K d : R) :
  0 <= K -> 0 <= d ->
  (forall w, L0 (M0 w)=w) -> (forall v, M (L v)=v) ->
  (forall w, NX (M0 w) <= C*NY w) ->
  (forall w, NX (M w) <= K*NY w) ->
  (forall v, NY (L v-L0 v) <= d*NX v) ->
  forall w, NX (M w-M0 w) <= (K*d*C)*NY w.
Proof.
move=> hK hd hL0M0 hML hM0 hM hdiff w.
have heq : M w-M0 w = M (L0 (M0 w)-L (M0 w)).
  by rewrite linearB /= hL0M0 hML.
rewrite heq; apply: le_trans (hM _) _.
have herr : NY (L0 (M0 w)-L (M0 w)) <= d*NX (M0 w).
  rewrite (real_seminorm_subtract hNY.1); exact: hdiff.
have hh := ler_wpM2l hd (hM0 w).
have hb := ler_wpM2l hK (le_trans herr hh).
by rewrite !mulrA in hb.
Qed.
