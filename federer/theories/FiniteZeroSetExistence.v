(** Federer (1969), 3.4.5, p. 320: existence
    and uniqueness of the original finite-equation zero sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [original_zero_set_exists]: the set
    var(U,F) satisfying the independent original membership
    law exists, 3.4.5, p. 320. *)
Lemma original_zero_set_exists (A:zmodType) (X:Type) (U:set X) (I:finType) (f:I->X->A):
  exists S:set X,is_original_zero_set U f S.
Proof. exists (fun x=>U x /\forall i,f i x=0);constructor=>x;by split. Qed.

(** Source for [original_zero_set_unique]: the original
    simultaneous-equation law determines one set, 3.4.5, p. 320. *)
Lemma original_zero_set_unique (A:zmodType) (X:Type) (U:set X) (I:finType) (f:I->X->A) (S T:set X):
  is_original_zero_set U f S ->is_original_zero_set U f T ->S=T.
Proof.
move=>hS hT;apply/seteqP;split=>x.
- by rewrite (original_zero_set_membership hS x) (original_zero_set_membership hT x).
- by rewrite (original_zero_set_membership hS x) (original_zero_set_membership hT x).
Qed.
