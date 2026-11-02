(** Federer (1969), 2.5.13, p. 106: the lattice of continuous real functions
    with compact support, whose support is the closure of the nonzero locus.
    The local erratum has no correction to 2.5.13. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_function_support]: direct displayed support
    definition in Federer 2.5.13, p. 106. The function
    is total, as in the printed continuous-function lattice. *)
Definition real_function_support (R : realType) (X : topologicalType) (f : X -> R) :=
  closure [set x | f x <> 0].

(** Source for [compactly_supported_continuous_functions]: direct lattice L
    in Federer 2.5.13, p. 106 This predicate specifies continuity and
    compact support without choosing a presentation of the support. *)
Definition compactly_supported_continuous_functions (R : realType) (X : topologicalType) : set (X -> R) :=
  [set f | continuous (f : X -> real_line_metric R) /\ compact (real_function_support f)].

(** Source for [real_function_support_closed]: supporting closedness
    of the support in Federer 2.5.13, p. 106, directly
    from its closure definition. *)
Lemma real_function_support_closed (R : realType) (X : topologicalType) (f : X -> R) :
  closed (real_function_support f).
Proof. exact: closed_closure. Qed.

(** Source for [real_function_zero_off_support]: supporting vanishing
    outside the support used in the last estimate of Federer 2.5.13, p. 107 *)
Lemma real_function_zero_off_support (R : realType) (X : topologicalType) (f : X -> R) x :
  ~ real_function_support f x -> f x=0.
Proof.
move=> hx; apply: contrapT=> hf; apply: hx; exact: subset_closure hf.
Qed.

(** Source for [real_function_support_in_closed_set]: supporting
    containment criterion for the compact support in Federer
    2.5.13, p. 106. A closed set outside which the
    function vanishes contains its support. *)
Lemma real_function_support_in_closed_set (R : realType) (X : topologicalType)
    (f : X -> R) (K : set X) :
  closed K -> (forall x, ~ K x -> f x=0) -> real_function_support f `<=` K.
Proof.
move=> hK hz; rewrite ((closure_id K).1 hK); apply: closureS=> x hx.
apply: contrapT=> hn; apply: hx; exact: hz hn.
Qed.

(** Source for [real_function_compact_support_in_closed_set]:
    supporting compact-support criterion for Federer 2.5.13,
    p. 106, by closed-subset compactness. *)
Lemma real_function_compact_support_in_closed_set (R : realType) (X : topologicalType)
    (f : X -> R) (K : set X) :
  compact K -> closed K -> (forall x, ~ K x -> f x=0) -> compact (real_function_support f).
Proof.
move=> hK hc hz; apply: (@subclosed_compact X (real_function_support f) K
  (@real_function_support_closed R X f) hK).
exact: real_function_support_in_closed_set hc hz.
Qed.
