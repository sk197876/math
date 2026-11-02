(** Private existence construction for Federer (1969),
    3.2.16, p. 253, and erratum p. 5,
    line 29. Finite minima and quarter powers
    witness the independent strict half-radius laws.
    Only the sealing module and audit may import it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import ShrinkingRadiusSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [shrinking_radius_selection_exists]:
    existence of the corrected radii in Federer
    3.2.16, p. 253. Every downward stable
    property with a positive radius at each
    index admits such a sequence; no choice
    or recurrence is postulated as a project axiom. *)
Theorem shrinking_radius_selection_exists (R : realType)
    (P : nat -> R -> Prop) :
  (forall n, exists r : R, 0<r /\ P n r) ->
  (forall n (r s : R), 0<s<=r -> P n r -> P n s) ->
  exists rho, is_shrinking_radius_selection P rho.
Proof.
move=> hSmall hDown.
have [b hb] := choice hSmall.
pose w := fix w (n : nat) : R :=
  match n with 0%N => Num.min 1 (b 0%N) | k.+1 => Num.min (w k) (b k.+1) end.
have hw0 : w 0%N=Num.min 1 (b 0%N) by [].
have hwS n : w n.+1=Num.min (w n) (b n.+1) by [].
have hwPos n : 0<w n.
  elim: n=> [|n IH].
  - by rewrite hw0 lt_min ltr01 (hb 0%N).1.
  - by rewrite hwS lt_min IH (hb n.+1).1.
have hwOwn n : w n<=b n.
  case: n=> [|n]; [rewrite hw0|rewrite hwS]; by rewrite ge_min lexx orbT.
have hwStep n : w n.+1<=w n by rewrite hwS ge_min lexx.
pose q := (1/4 : R).
have hq : 0<q by rewrite /q; lra.
have hq1 : q<=1 by rewrite /q; lra.
pose rho n := q^+n.+1*w n.
have hRhoPos n : 0<rho n.
  apply: mulr_gt0; last exact: hwPos.
  apply: exprn_gt0; exact hq.
have hRhoOwn n : rho n<=b n.
  apply: le_trans _ (hwOwn n).
  have hh := ler_wpM2r (ltW (hwPos n)) (exprn_ile1 n.+1 (ltW hq) hq1).
  by rewrite mul1r in hh.
have hRhoStep n : rho n.+1<=q*rho n.
  rewrite /rho exprS mulrA.
  exact: (ler_wpM2l (mulr_ge0 (ltW hq) (exprn_ge0 n.+1 (ltW hq))) (hwStep n)).
exists rho; constructor.
- exact: hRhoPos.
- move=> n; apply: (hDown n (b n) (rho n)); last exact: (hb n).2.
  by apply/andP; split; [exact: hRhoPos|exact: hRhoOwn].
- move=> n; have hStep := hRhoStep n; have hPos := hRhoPos n.
  have hStrict : q*rho n<rho n/2 by rewrite /q; lra.
  exact: le_lt_trans hStep hStrict.
Qed.
