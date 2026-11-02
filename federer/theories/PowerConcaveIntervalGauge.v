(** Federer (1969), 2.10.28, pp. 191, 193: the positive multiple c*t^m is an
    admissible gauge for 0<m<1. Leave c arbitrary and positive; the book
    chooses alpha(m)*2^-m. This does not identify the project’s pending
    real-degree Gamma normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerContinuity FractionalPowerConcavity ConcaveIntervalGaugeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [power_concave_interval_gauge]: direct
    concave power gauge in 2.10.28, p. 191,
    allowing any positive normalising constant.
    The total power representative is used only
    on nonnegative lengths; the formal laws
    include continuity from the right at zero. *)
Theorem power_concave_interval_gauge (R : realType) (c m : R) :
  0<c -> 0<m -> m<1 -> is_concave_interval_gauge (fun t=>c*real_power t m).
Proof.
move=> hc hm hm1; constructor.
- by rewrite real_power_zero_base ?gt_eqF // mulr0.
- move=> a b ha hab; exact (ler_wpM2l (ltW hc) (@real_power_monotone R a b m ha hab hm)).
- move=> a b t ha hb hab ht ht1.
  have hh := @fractional_power_strict_concavity R m a b t hm hm1 ha hb hab ht ht1.
  have hmul : c*((1-t)*real_power a m+t*real_power b m)<c*real_power ((1-t)*a+t*b) m.
    by rewrite (ltr_pM2l hc).
  have he : (1-t)*(c*real_power a m)+t*(c*real_power b m)=
      c*((1-t)*real_power a m+t*real_power b m) by lra.
  by rewrite he.
- move=> x e hx he.
  have hediv : 0<e/c by rewrite divr_gt0.
  have [d hd hnear] := @real_power_local_bound R x m (e/c) hx hm hediv.
  exists d; split=> // y hy hdist.
  have hsmall : `|x-y|<d by rewrite distrC.
  have hh := hnear y hy hsmall.
  have hmul : c*`|real_power x m-real_power y m|<e.
    move: hh; by rewrite ltr_pdivlMr // mulrC.
  rewrite -mulrBr normrM (ger0_norm (ltW hc)) distrC; exact hmul.
Qed.
