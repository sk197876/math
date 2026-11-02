(** Federer (1969), 2.1.6(2), pp. 58-59: the successor of an Ulam cardinal
    is Ulam. We prove the theorem for abstract cardinal representatives,
    then obtain the required small-prefix representative from the general
    well-ordering principle. No external measure theorem or unproved
    cardinal axiom is used. The matrix proof uses the correction a in alpha
    from Federer's erratum p. 1, book p. 59 line 3. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal wochoice.
From Federer Require Import UlamCardinalUP CardinalSuccessorUP
  WellOrderLaws CardinalSuccessorPrefixes UlamSmallPrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [ulam_set_successor]: Federer 2.1.6(2),
    pp. 58-59, direct formalisation: every successor of an Ulam
    cardinal is Ulam. The general well-ordering principle supplies
    a representative with small proper initial segments, and the
    local matrix argument establishes its Ulam property. *)
Theorem ulam_set_successor (R : realType) (I J : choiceType)
    (A : set I) (B : set J) :
  is_ulam_set R A -> is_cardinal_successor A B -> is_ulam_set R B.
Proof.
move=> hu hs; have [r hw] := well_ordering_principle J.
have [C [hCB [hBC hp]]] := cardinal_successor_small_prefixes hs hw.
apply: ulam_set_downward hBC _.
apply: (@ulam_set_small_prefixes R I J A C r hu _ hp).
move=> x y _ _; exact: (@well_order_total_law J r hw x y).
Qed.
