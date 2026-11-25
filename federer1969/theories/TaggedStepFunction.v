(** Public tagged step maps supporting Federer (1969), 2.9.24, p. 169. These
    consequences use only the sealed cell laws; no downstream proof unfolds
    the existence construction. Source context and conventions:
    TaggedStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TaggedStepFunctionUP TaggedStepFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [tagged_step_function]: supporting abstract step
    function for Federer 2.9.24, p. 169, with arbitrary
    tags; right tags recover the printed approximation. *)
Definition tagged_step_function := @TaggedStepFunction.value.

(** Source for [tagged_step_function_specification]: supporting
    cell specification for the map used in Federer 2.9.24,
    p. 169. Values outside the partition cells are zero. *)
Lemma tagged_step_function_specification (R : realType) (f : R -> R) (w : seq R) :
  is_tagged_step_function f w (@tagged_step_function R f w).
Proof. exact: TaggedStepFunction.laws. Qed.

(** Source for [tagged_step_function_cons]: supporting first-cell
    law for the approximation in Federer 2.9.24, p. 169.
    Empty cells leave the recursively specified remaining cells. *)
Lemma tagged_step_function_cons (R : realType) (f : R -> R)
    (a r b : R) (rest : seq R) (x : R) :
  tagged_step_function f (a::r::b::rest) x=
    if a<x<=b then f r else tagged_step_function f (b::rest) x.
Proof.
have [u [hu he]] := tagged_step_function_specification f (a::r::b::rest).
have hU := @tagged_step_function_unique R f (b::rest) u
  (tagged_step_function f (b::rest)) hu (tagged_step_function_specification f (b::rest)).
by rewrite (he x) hU.
Qed.

(** Source for [tagged_step_function_short]: supporting empty-
    cell convention for Federer 2.9.24, p. 169. Lists of
    at most two terms have no tagged cell and define zero. *)
Lemma tagged_step_function_short (R : realType) (f : R -> R) (w : seq R) :
  (size w<=2)%N -> forall x : R, tagged_step_function f w x=0.
Proof.
case: w=> [|a [|r [|b rest]]] hs x.
- exact: (@tagged_step_function_specification R f [::] x).
- exact: (@tagged_step_function_specification R f [:: a] x).
- exact: (@tagged_step_function_specification R f [:: a;r] x).
- by move: hs; rewrite /=.
Qed.
