(** Federer (1969), 2.5.3, p. 94, first display: normalised truncation
    differences approximate a strict level's characteristic function. These
    supporting scalar laws precede the measure and integral argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeRamp MonotoneDaniellIntegralUP
  RealLatticeTruncationLimits ExtendedRealOrderLimit ExtendedRealReciprocalBounds
  CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_lattice_level_ramp_clipped]: Supporting Federer 2.5.3,
    p. 94.This branch assumes f(x)>=t; below t the ramp is zero. *)
Lemma real_lattice_level_ramp_clipped (R : realType) (X : Type)
    (f : X -> R) (t h : R) x :
  0 < h -> t <= f x ->
  real_lattice_ramp f t (t+h) x=Order.min (h^-1 * (f x-t)) 1.
Proof.
move=> hh ht.
have hcancel : t+h-t=h by rewrite addrAC subrr add0r.
rewrite /real_lattice_ramp hcancel (min_r ht).
case: (leP (f x) (t+h))=> hf.
- rewrite min_l // (@ler_pdivrMl R h 1 (f x-t) hh) mulr1 lerBlDr addrC; exact hf.
- rewrite hcancel mulVf ?gt_eqF //.
  rewrite min_r // (@ler_pdivlMl R h 1 (f x-t) hh) mulr1 lerBrDr addrC; exact: ltW hf.
Qed.

(** Source for [real_lattice_level_ramp_width_antitone]: increasing
    approximants as h decreases to zero in Federer 2.5.3, p. 94 This holds
    for arbitrary f and threshold, before lattice membership. *)
Lemma real_lattice_level_ramp_width_antitone (R : realType) (X : Type)
    (f : X -> R) (t h k : R) :
  0 < h -> 0 < k -> h <= k ->
  function_le (real_lattice_ramp f t (t+k)) (real_lattice_ramp f t (t+h)).
Proof.
move=> hh hk hhk x.
have hth : t <= t+h by rewrite lerDl; exact: ltW hh.
have htk : t <= t+k by rewrite lerDl; exact: ltW hk.
case: (leP (f x) t)=> ht.
- by rewrite (real_lattice_ramp_zero htk ht) (real_lattice_ramp_zero hth ht).
- rewrite (@real_lattice_level_ramp_clipped R X f t k x hk (ltW ht))
    (@real_lattice_level_ramp_clipped R X f t h x hh (ltW ht)).
  rewrite [Order.min (_ * _) 1]minC [in leRHS]minC.
  apply: real_minimum_ceiling_monotone.
  apply: ler_wpM2r; first by rewrite subr_ge0; exact: ltW ht.
  by rewrite (@lef_pV2 R k h hk hh).
Qed.

(** Source for [real_lattice_reciprocal_level_ramps_increase]:
    characteristic approximation for the strict level in Federer 2.5.3, p.
    94 The reciprocal widths are cofinal at zero. For each point the
    sequence is eventually exactly its characteristic value. *)
Lemma real_lattice_reciprocal_level_ramps_increase (R : realType) (X : Type)
    (f : X -> R) (t : R) (s : X -> R) :
  is_characteristic_function [set x | t < f x] s ->
  real_functions_increase_to
    (fun n => real_lattice_ramp f t (t+((n.+1)%:R)^-1)) s.
Proof.
move=> hs x; split.
- move=> n m hnm; rewrite lee_fin.
  apply: real_lattice_level_ramp_width_antitone; first by rewrite invr_gt0 ltr0n.
  + by rewrite invr_gt0 ltr0n.
  + exact: positive_reciprocal_nat_antitone hnm.
- have he : exists N, forall n, (N <= n)%N ->
      real_lattice_ramp f t (t+((n.+1)%:R)^-1) x=s x.
    case: (boolP (t < f x))=> ht.
    + have hdiff : 0 < f x-t by rewrite subr_gt0.
      have [N hN] := positive_reciprocal_nat_small hdiff.
      exists N=> n hn.
      rewrite (characteristic_on_set hs ht); apply: real_lattice_ramp_one.
      * by rewrite ltrDl invr_gt0 ltr0n.
      * have hsmall := le_lt_trans (@positive_reciprocal_nat_antitone R N n hn) hN.
        apply: ltW; by move: hsmall; rewrite ltrBrDl addrC.
    + exists 0%N=> n _; rewrite (characteristic_off_set hs (fun h => (negP ht) h)).
      apply: real_lattice_ramp_zero; first by rewrite lerDl invr_ge0 ler0n.
      by rewrite leNgt ht.
  have [N hN] := he; split; move=> a ha; exists N=> n hn; by rewrite hN.
Qed.
