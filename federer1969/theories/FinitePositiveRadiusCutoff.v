(** Federer (1969), 3.2.39, p. 276: finite
    radius estimates hold on one common positive neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_common_positive_radius_bound]: supporting
    finite passage to upper and lower limits in Federer
    3.2.39, p. 276. Only local proved cutoffs are
    selected. Their finite minimum is positive even for an
    empty index type, where a unit cutoff suffices. *)
Lemma finite_common_positive_radius_bound (R:realType) (I:finType) (P:I->R->Prop):
  (forall i,exists d:R,0<d /\forall r:R,0<r<d ->P i r) ->
  exists d:R,0<d /\forall r:R,0<r<d ->forall i,P i r.
Proof.
move=>hExists.
pose d i:=projT1 (cid (hExists i)).
have hD i:0<d i /\forall r:R,0<r<d i ->P i r:=projT2 (cid (hExists i)).
pose delta:=\big[Order.min/1]_(i:I) d i.
have hDelta:0<delta.
  rewrite /delta; apply:(big_ind (fun t:R=>0<t)); first exact:ltr01.
  - by move=>a b ha hb; rewrite lt_min ha hb.
  - move=>i _; exact:(hD i).1.
exists delta; split=>// r /andP[hr hSmall] i.
apply:(hD i).2; apply/andP; split=>//.
exact:lt_le_trans hSmall (bigmin_le (1:R) i d).
Qed.
