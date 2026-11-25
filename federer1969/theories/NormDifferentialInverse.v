(** Federer (1969), 3.1.1(1), p. 209: differentiate a local inverse.
    The inverse is supplied with its laws; this theorem does not assume
    differentiability of the inverse or completeness of either space. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_inverse]: Federer 3.1.1(1), p. 209.
    In words: the differential of a local inverse is the inverse of the
    differential. We expose the inverse-domain neighbourhood, inverse
    identities and continuity at the image point as hypotheses. Only the
    left inverse identity for the linear maps is needed in this proof;
    a linear homeomorphism supplies it and the finite bound for M. *)
Theorem norm_differential_inverse (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X -> Prop) (B : Y -> Prop) (f : X -> Y) (g : Y -> X)
    (a : X) (L : Hom X Y) (M : Hom Y X) :
  has_norm_differential NX NY A f a L ->
  norm_bounded_linear NY NX M ->
  (forall x, M (L x) = x) ->
  norm_domain_interior NY B (f a) ->
  g (f a) = a ->
  (forall y, B y -> A (g y) /\ f (g y) = y) ->
  (forall r : R, 0 < r -> exists d : R, 0 < d /\
    forall k, B (f a+k) -> NY k < d -> NX (g (f a+k)-a) < r) ->
  has_norm_differential NY NX B g (f a) M.
Proof.
move=> hf hM hML hB hga hfg hgc; split=> // e he.
have [C [hC hMC]] := hM.
pose D := C+1.
have hD : 0 < D by rewrite /D; lra.
have hMD : forall y, NX (M y) <= D*NY y.
  move=> y; apply: le_trans (hMC y) _.
  apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNY.1 y.
  rewrite /D; lra.
have htwoD : 0 < 2*D by rewrite mulr_gt0.
have htwoDD : 0 < 2*D*D by rewrite mulr_gt0.
pose p := Num.min (1/(2*D)) (e/(2*D*D)).
have hp : 0 < p by rewrite /p lt_min !divr_gt0 // ltr01 he.
have hp1 : p <= 1/(2*D) by rewrite /p ge_min lexx.
have hp2 : p <= e/(2*D*D) by rewrite /p ge_min lexx orbT.
have hpD : p*(2*D) <= 1 by move: hp1; rewrite ler_pdivlMr.
have hpDD : p*(2*D*D) <= e by move: hp2; rewrite ler_pdivlMr.
have [r [hr hrf]] := norm_differential_remainder hf hp.
have [d [hd hgd]] := hgc r hr.
exists d; split=> // k hbk hk.
pose h := g (f a+k)-a.
have hshift : a+h = g (f a+k) by rewrite /h addrC subrK.
have [hag hfgk] := hfg _ hbk.
have hah : A (a+h) by rewrite hshift.
have hsmall : NX h < r := hgd k hbk hk.
have hfr := hrf h hah hsmall.
have heqk : f (a+h)-f a = k by rewrite hshift hfgk addrAC subrr add0r.
rewrite heqk in hfr.
have hnX := real_seminorm_nonnegative hNX.1 h.
have hnY := real_seminorm_nonnegative hNY.1 k.
have htri : NY (L h) <= NY k + NY (k-L h).
  have heq : L h = k + -(k-L h) by rewrite opprB addrC subrK.
  rewrite {1}heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  by rewrite (real_seminorm_negate hNY.1).
have hlin : NX h <= D * (NY k + p*NX h).
  rewrite -{1}(hML h); apply: le_trans (hMD (L h)) _.
  apply: ler_wpM2l; first exact: ltW hD.
  exact: le_trans htri (lerD (lexx _) hfr).
have hinv : NX h <= (2*D)*NY k by nra.
have herr : NX (h-M k) <= D*(p*NX h).
  have heq : h-M k = -(M (k-L h)).
    by rewrite linearB /= opprB hML.
  rewrite heq (real_seminorm_negate hNX.1).
  apply: le_trans (hMD _) _.
  apply: ler_wpM2l; first exact: ltW hD.
  exact hfr.
rewrite hga; change (NX (h-M k) <= e*NY k).
apply: le_trans herr _.
have hstep : D*(p*NX h) <= D*(p*((2*D)*NY k)).
  apply: ler_wpM2l; first exact: ltW hD.
  apply: ler_wpM2l; first exact: ltW hp.
  exact hinv.
apply: le_trans hstep _.
have halg : D*(p*((2*D)*NY k)) = (p*(2*D*D))*NY k by ring.
rewrite halg; apply: ler_wpM2r=> //.
Qed.
