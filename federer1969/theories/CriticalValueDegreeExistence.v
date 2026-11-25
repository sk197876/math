(** Federer (1969), 3.4.1, p. 310: existence and uniqueness of the printed critical degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import CriticalValueDegreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [critical_value_degree_exists]: the displayed scalar in
    3.4.1, p. 310, exists. Its formula is used only to establish the
    independent equation; public estimates use the sealed equation law. *)
Lemma critical_value_degree_exists (R:realType) m nu k:
  exists s:R,is_critical_value_degree m nu k s.
Proof. exists (nu%:R+(m%:R-nu%:R)/k%:R);by constructor. Qed.

(** Source for [critical_value_degree_unique]: the defining equation in
    3.4.1, p. 310, uniquely determines the scalar. This is independent of
    the theorem asserting nullity and the later sharpness example. *)
Lemma critical_value_degree_unique (R:realType) m nu k (s t:R):
  is_critical_value_degree m nu k s ->is_critical_value_degree m nu k t ->s=t.
Proof. move=>hs ht;by rewrite (critical_value_degree_equation hs) (critical_value_degree_equation ht). Qed.
