(** Federer (1969), 3.3.4, pp. 289–292:
    choose one actual aperture window compatible
    with a positive rescaling and an independent
    original cutoff. This supporting scalar
    existence lemma never selects a global radius. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_scaled_radius_window]:
    the common small-aperture interval supporting
    the aperture and ball comparisons in Federer
    3.3.4, pp. 289–292. Every positive
    rescaling and both original strict cutoffs
    are retained. *)
Lemma structure_scaled_radius_window (R:realType) (a b c:R):
  0<a ->0<b ->0<c ->exists d:R,0<d /\
    forall s:R,0<s<d ->0<s<a /\ 0<c*s<b.
Proof.
move=>ha hb hc; exists (Num.min a (b/c)); split.
- by rewrite lt_min ha divr_gt0.
- move=>s /andP [hs hsd].
  have hdA:Num.min a (b/c)<=a by rewrite ge_min lexx.
  have hdB:Num.min a (b/c)<=b/c by rewrite ge_min lexx orbT.
  have hsA:s<a:=lt_le_trans hsd hdA.
  have hsB:s<b/c:=lt_le_trans hsd hdB.
  have hcS:0<c*s by rewrite mulr_gt0.
  have hSmall:c*s<b by move:hsB; rewrite (ltr_pdivlMr _ _ hc) mulrC.
  by split; apply/andP.
Qed.
