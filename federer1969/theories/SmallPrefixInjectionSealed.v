(** Opaque interface for the cardinal comparison supporting Federer (1969),
    2.5.11, p. 102, where sets Y_j with cardinal number aleph_j are
    presupposed. Source context and the transfinite argument:
    SmallPrefixInjectionConstruction.v. The implementation proves the
    signature law; it is not a new axiom. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP SmallPrefixInjectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

Module Type SmallPrefixInjectionSignature.
(** Source for [injects]: supporting comparison for the sets Y_j
    of Federer 2.5.11, p. 102: a well ordered set whose proper
    initial segments have cardinal at most that of A has cardinal
    at most that of every set B whose cardinal is not at most that
    of A (Kelley, Appendix, Theorems 150 and 157, p. 275). *)
Parameter injects : forall (I J K : choiceType) (A : set I) (D : set J) (r : rel J) (B : set K),
  well_order r -> (forall x, D x -> well_order_prefix D r x #<= A) -> ~ (B #<= A) -> D #<= B.
End SmallPrefixInjectionSignature.

Module SmallPrefixInjection : SmallPrefixInjectionSignature.
(** Source for [injects]: the proved transfinite selection
    discharges the signature law for Federer 2.5.11, p. 102. *)
Theorem injects (I J K : choiceType) (A : set I) (D : set J) (r : rel J) (B : set K) :
  well_order r -> (forall x, D x -> well_order_prefix D r x #<= A) -> ~ (B #<= A) -> D #<= B.
Proof. exact: small_prefix_injects_exists. Qed.
End SmallPrefixInjection.
