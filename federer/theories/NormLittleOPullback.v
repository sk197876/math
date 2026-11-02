(** Federer (1969), 3.1.11, p. 222: the remainder of the
    outer Taylor polynomial stays negligible when evaluated on an
    inner increment of order O(|t|). This is a supporting estimate
    for the printed composition-of-jets limit. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP NormLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_little_o_power_pullback]: the first error term
    in replacing g composed with f by the composition of the two
    jets, Federer 3.1.11, p. 222. The local remainder inequality
    includes zero increments, so the inner curve may return to zero.
    Zero order and a zero growth constant are included. *)
Lemma norm_little_o_power_pullback (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (rho : X->Y) (v : R->X) k C r :
  0<=C -> 0<r ->
  (forall t, `|t|<r -> NX (v t)<=C*`|t|) ->
  (forall e : R, 0<e -> exists d : R, 0<d /\
    forall h, NX h<d -> NY (rho h)<=e*(NX h)^+k) ->
  norm_little_o_power NY (fun t=>rho (v t)) k.
Proof.
move=>hC hr hv hrem e he.
pose B := C+1.
have hB : 0<B by rewrite /B; lra.
have hCB : C<=B by rewrite /B; lra.
have hBk : 0<B^+k := exprn_gt0 k hB.
have heB : 0<e/B^+k by rewrite divr_gt0.
have [d [hd hb]] := hrem (e/B^+k) heB.
exists (Num.min r (d/B)); split; first by rewrite lt_min hr divr_gt0.
move=>t /andP [ht0 ht].
have /andP [htr htd] : (`|t|<r)&&(`|t|<d/B) by rewrite -lt_min.
have hvt : NX (v t)<=B*`|t|.
  exact (le_trans (hv t htr) (ler_wpM2r (normr_ge0 t) hCB)).
have hsmall : NX (v t)<d.
  apply: le_lt_trans hvt _; by move:htd; rewrite ltr_pdivlMr // mulrC.
apply: le_trans (hb _ hsmall) _.
have hpow := lerXn2r k (real_seminorm_nonnegative hNX.1 (v t))
  (mulr_ge0 (ltW hB) (normr_ge0 t)) hvt.
have hh := ler_wpM2l (ltW heB) hpow.
by rewrite exprMn mulrA divfK ?gt_eqF // in hh.
Qed.
