(** Set-theoretic infrastructure for Federer (1969), 2.1.6, pp. 58-59.
    Cardinal comparison is represented by injections between subsets. The
    adapter below merely supplies a total ambient function, using a
    specified default outside its domain. Kelley, General Topology,
    Appendix, pp. 275-276, gives the underlying cardinal-comparison
    convention (local Dover 2017 reprint of 1955). *)
From mathcomp Require Import all_boot boolp classical_sets functions cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [cardinal_injection_with_default]: supporting
    infrastructure for Federer's injections in 2.1.6, p. 59, not
    a separate claim in the book. An injection of subsets extends
    to an ambient function by assigning a default outside the source. *)
Lemma cardinal_injection_with_default (I J : choiceType)
    (A : set I) (B : set J) (d : J) :
  A #<= B -> exists f : I -> J, set_fun A B f /\ set_inj A f.
Proof.
move=> /card_leP [f]; exists (valLR d f); split.
- exact: funS.
- exact: inj.
Qed.

(** Source for [cardinal_bound_of_injection]: supporting
    infrastructure for Federer 2.1.6, pp. 58-59, using cardinal
    comparison by injection (Kelley Appendix, pp. 275-276).
    A function mapping A into B and injective on A proves the bound. *)
Lemma cardinal_bound_of_injection (I J : choiceType) (A : set I)
    (B : set J) (f : I -> J) : set_fun A B f -> set_inj A f -> A #<= B.
Proof.
move=> hf hi; have [g] : $|{injfun A >-> B}|.
  apply/injfunPex; by exists f.
exact: inj_card_le g.
Qed.
