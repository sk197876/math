(** Federer (1969), 2.5.14, p. 108, final paragraph: notation K(X) for the
    compact-support function lattice and the support of its Daniell
    integral. The existing predicate
    compactly_supported_continuous_functions already denotes K(X). *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_daniell_support]: direct final displayed
    support definition in Federer 2.5.14, p. 108 The functional's vanishing
    law is tested only on its domain K(X); no values of the ambient
    representative outside K(X) enter the definition. *)
Definition compact_support_daniell_support (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) : set X :=
  ~` (\bigcup_(W in [set W | open W /\ forall f,
    compactly_supported_continuous_functions f -> real_function_support f `<=` W -> A f=0]) W).

(** Source for [compact_support_daniell_support_closed]: Federer
    2.5.14, p. 108, calls this support a closed set.
    Closedness follows from the union of its open null neighborhoods,
    independently of the functional's additive or continuity laws. *)
Lemma compact_support_daniell_support_closed (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) : closed (compact_support_daniell_support A).
Proof.
rewrite /compact_support_daniell_support closedC; apply: bigcup_open=> W [hW _]; exact hW.
Qed.
