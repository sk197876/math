(** Federer (1969), 3.2.41, printed p. 277, finite-family
    induction: retain at most one nonempty cut of each original
    member, and omit an entire member on each side of the first
    cut. These supporting finite-index facts justify strict descent. *)
From mathcomp Require Import all_boot all_order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [finite_predicate_restriction_cardinality]: supporting
    card(H_k)<=card(H) in Federer 3.2.41, p. 277. The finite
    subtype retains one original index exactly when its predicate holds. *)
Lemma finite_predicate_restriction_cardinality (I:finType) (P:pred I):
  #|{: {i:I|P i}}|<=#|I|.
Proof. by rewrite card_sub; exact:max_card. Qed.

(** Source for [finite_predicate_restriction_strict_cardinality]:
    supporting card(G_k)<card(G) in Federer 3.2.41, p. 277.
    An actually excluded original index gives a proper subset;
    no cardinality bound is assumed as a cut law. *)
Lemma finite_predicate_restriction_strict_cardinality (I:finType) (P:pred I) (i:I):
  ~~P i ->#|{: {j:I|P j}}|<#|I|.
Proof.
move=> hi; rewrite card_sub.
apply:proper_card; apply/properP; split; first exact:subset_predT.
exists i; first by [].
by rewrite inE.
Qed.

(** Source for [finite_predicate_restriction_positive_cardinality]:
    supporting nonempty cut families in Federer 3.2.41, p. 277.
    An included original member supplies a genuine subtype index. *)
Lemma finite_predicate_restriction_positive_cardinality (I:finType) (P:pred I) (i:I):
  P i ->0<#|{: {j:I|P j}}|.
Proof.
move=> hi; rewrite card_sub; apply/card_gt0P; exists i; by rewrite inE.
Qed.

(** Source for [finite_type_two_distinct_members]: supporting choice
    of two disjoint original boxes when card(G)>1 in Federer
    3.2.41, p. 277. This is finite-set background only. *)
Lemma finite_type_two_distinct_members (I:finType):
  1<#|I| ->exists i j:I,i!=j.
Proof.
move/card_gt1P=>[i [j [_ _ hNe]]]; by exists i,j.
Qed.
