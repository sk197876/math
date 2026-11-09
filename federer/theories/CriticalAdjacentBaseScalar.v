(** Federer (1969), 3.3.20, p. 308:
    the initial adjacent-parent Omega estimates imply the half-sigma reduction. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_adjacent_base_scalar_bridge]:
    the initial scalar chain in 3.3.20,
    p. 308. Actual diameter at least
    one half, the original strict r_2 count
    and the two proved original Omega implications
    give diameter at least sqrt(2)/2.
    The successive strict thresholds eleven and
    nine and the 11/16 and 7/8
    distances are retained. Geometry is discharged
    separately before use in the numbered theorem. *)
Theorem critical_adjacent_base_scalar_bridge (R:realType) (d:R) (r:nat):
  1/2<=d ->(r%:R:R)<16*(1-d/Num.sqrt 2) ->
  ((r<12)%N ->(11/16:R)<=d) ->((r<9)%N ->(7/8:R)<=d) ->
  Num.sqrt (2:R)/2<=d.
Proof.
move=>hHalf hMissing hFour hOne.
pose s:=Num.sqrt (2:R).
have hs:0<s by rewrite /s sqrtr_gt0 ltr0n.
have hs2:s^+2= 2 by rewrite /s sqr_sqrtr // ler0n.
have hsNZ:s!=0 by rewrite gt_eqF.
pose sigma:=1-d/s.
change (is_true ((r%:R:R)<16*sigma)) in hMissing.
have hSigma:sigma*s=s-d by rewrite /sigma;field;by rewrite hsNZ.
have hUpper:s<8/5 by nra.
have hInitial:sigma<11/16 by nra.
have hCount11:(r<11)%N.
  have h:(r%:R:R)<11 by nra.
  by move:h;rewrite ltr_nat.
have hCount12:(r<12)%N:=ltn_trans hCount11 (erefl true:(11<12)%N).
have hDistance:=hFour hCount12.
have hUpper2:s<11/7 by nra.
have hNext:sigma<9/16 by nra.
have hCount9:(r<9)%N.
  have h:(r%:R:R)<9 by nra.
  by move:h;rewrite ltr_nat.
have hDistance2:=hOne hCount9.
change (is_true (s/2<=d));nra.
Qed.
