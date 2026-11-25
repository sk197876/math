(** Federer (1969), proof of 2.4.4(2), p. 83: U<=t*L for every real t>1
    forces U<=L when L>=0. We use strict rational density to prove it
    without importing a theorem about integrals. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_geometric_squeeze]: supporting final
    inference from the multiplicative bounds in Federer
    2.4.4(2), p. 83, including L=0 and L=infinity. *)
Lemma extended_geometric_squeeze (R : realType) (L U : \bar R) :
  0 <= L -> (forall t : R, (1 < t)%R -> U <= t%:E*L) -> U <= L.
Proof.
case: L=> [b| |] hL hU; [|exact: leey|by move: hL; rewrite leNgt ltNyr].
have hb : (0 <= b)%R := hL.
have [hb0|hb0] := eqVneq b 0%R.
- rewrite hb0; have h := hU 2%R (ltr1n _ 2).
  by rewrite hb0 mule0 in h.
- have hbp : (0 < b)%R by rewrite lt_neqAle eq_sym hb0 hb.
  rewrite leNgt; apply/negP=> hbad.
  have [q [hl hr]] := @extended_rationals_order_dense R b%:E U hbad.
  have hq : (b < ratr q)%R by move: hl; rewrite lte_fin.
  have ht : (1 < (ratr q : R)/b)%R by rewrite ltr_pdivlMr // mul1r.
  have h := hU ((ratr q : R)/b)%R ht.
  rewrite -EFinM divfK // in h.
  by move: hr; rewrite ltNge h.
Qed.
