(** Federer (1969), 3.1.11, p. 222: a fixed multiple of a
    negligible remainder is negligible. This estimate controls the
    change of the outer polynomial when its argument is replaced by
    the inner jet. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_little_o_power_domination]: the local Lipschitz
    estimate in the composition-of-jets limit, Federer 3.1.11,
    p. 222. A locally bounded multiple of a remainder of order
    o(|t|^k) has the same order. The constant may be zero. *)
Lemma norm_little_o_power_domination (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (f : R->X) (g : R->Y) k C r :
  0<=C -> 0<r ->
  (forall t, 0<`|t|<r -> NY (g t)<=C*NX (f t)) ->
  norm_little_o_power NX f k -> norm_little_o_power NY g k.
Proof.
move=>hC hr hb hf e he.
pose B := C+1.
have hB : 0<B by rewrite /B; lra.
have hCB : C<=B by rewrite /B; lra.
have heB : 0<e/B by rewrite divr_gt0.
have [d [hd hdB]] := hf (e/B) heB.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>t /andP [ht0 ht].
have /andP [htr htd] : (`|t|<r)&&(`|t|<d) by rewrite -lt_min.
apply: le_trans (hb t (introT andP (conj ht0 htr))) _.
apply: le_trans (ler_wpM2r (real_seminorm_nonnegative hNX.1 (f t)) hCB) _.
have hh := ler_wpM2l (ltW hB) (hdB t (introT andP (conj ht0 htd))).
by rewrite mulrA [B*(e/B)]mulrC divfK ?gt_eqF // in hh.
Qed.
