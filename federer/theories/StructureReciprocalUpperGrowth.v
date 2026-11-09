(** Federer (1969), 3.3.9, pp. 295–296: supporting
    scalar inverse-aperture growth for a concrete finite-mass regression. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal lra.
From Federer Require Import PositiveRadiusLimits ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_reciprocal_upper_growth]: supporting
    ordinary inverse-aperture unboundedness in the original upper
    cone-growth condition of Federer 3.3.9, pp. 295–296.
    A reciprocal lower bound on every sufficiently small positive
    aperture forces the full positive-radius upper limit to infinity.
    The independent order laws, rather than a sampled limit, are used. *)
Lemma structure_reciprocal_upper_growth (R:realType) (f:R->\bar R) (t:R):
  0<t ->(forall s,0<s<t ->((s^-1)%:E<=f s)%E) ->
  positive_radius_upper_limit f=+oo%E.
Proof.
move=>ht hLower; apply/eqP; rewrite eq_le leey /=.
apply:extended_real_inf_greatest=>v [d [hd ->]].
have hAbove b:(b%:E<extended_real_sup (positive_radius_values f d))%E.
  pose c:=Num.max b 0+1.
  have hbMax:b<=Num.max b 0 by rewrite le_max lexx.
  have hMax0:0<=Num.max b 0 by rewrite le_max lexx orbT.
  have hc:0<c by rewrite /c; nra.
  have hbc:b<c by rewrite /c; nra.
  pose s:=Num.min (Num.min d t) c^-1/2.
  have hMin:0<Num.min (Num.min d t) c^-1 by rewrite !lt_min hd ht invr_gt0 hc.
  have hs:0<s by rewrite /s divr_gt0 // ltr0n.
  have hSmall:s<Num.min (Num.min d t) c^-1 by rewrite /s; nra.
  have hBoth:Num.min (Num.min d t) c^-1<=Num.min d t by rewrite ge_min lexx.
  have hD:Num.min d t<=d by rewrite ge_min lexx.
  have hT:Num.min d t<=t by rewrite ge_min lexx orbT.
  have hsd:s<d:=lt_le_trans hSmall (le_trans hBoth hD).
  have hst:s<t:=lt_le_trans hSmall (le_trans hBoth hT).
  have hMinInv:Num.min (Num.min d t) c^-1<=c^-1 by rewrite ge_min lexx orbT.
  have hInvSmall:s<c^-1:=lt_le_trans hSmall hMinInv.
  have hInv:c<s^-1.
    rewrite -[s^-1]div1r (ltr_pdivlMr _ _ hs).
    have hStrict:s*c<1.
      move:hInvSmall; by rewrite -[c^-1]div1r (ltr_pdivlMr _ _ hc).
    by rewrite mulrC.
  have hCost:(b%:E<f s)%E.
    apply:lt_le_trans _ (hLower s _); last by apply/andP; split.
    rewrite lte_fin; exact:lt_trans hbc hInv.
  apply:lt_le_trans hCost _; apply:extended_real_sup_upper.
  exists s; by split; first apply/andP; split.
case hValue:(extended_real_sup (positive_radius_values f d))=>[c| |].
- have hBad:=hAbove c; by rewrite hValue ltxx in hBad.
- exact:lexx.
- have hBad:=hAbove 0; by rewrite hValue in hBad.
Qed.
