(** Private existence proof for the tagged step functions supporting Federer
    (1969), 2.9.24, p. 169. The recursive construction serves only to prove
    the abstract cell specification. Source context and conventions:
    TaggedStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TaggedStepFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [tagged_step_function_exists]: supporting existence
    for the approximations of Federer 2.9.24, p. 169.
    Every finite tagged list has exactly the prescribed step map;
    no regularity assumption on f is needed for this finite choice. *)
Theorem tagged_step_function_exists (R : realType) (f : R -> R) (w : seq R) :
  exists v : R -> R, is_tagged_step_function f w v.
Proof.
have [n] := ubnP (size w).
elim: n w=> [//|n ih] [|a [|r [|b rest]]] hs /=;
  try by exists (fun _ => 0); move=> x.
have hsize : (size (b::rest)<n)%N by move: hs; rewrite /= !ltnS; exact: ltnW.
have [u hu] := ih (b::rest) hsize.
exists (fun x => if a<x<=b then f r else u x).
exists u; split=> // x.
Qed.
