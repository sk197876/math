(** Federer (1969), 2.9.24, p. 169: f_n takes a fixed tagged value on each
    left-open, right-closed partition cell. Right endpoint tags give the
    printed f_n. These abstract recursive cell laws precede a construction
    of the step map; they do not presume any measurability of f. The local
    Federer erratum has no entry for this step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_tagged_step_function]: supporting specification
    of the step functions in Federer 2.9.24, p. 169.
    The existing tagged lists store left endpoint, tag, right
    endpoint, tag, and so on. Each cell takes its tag value;
    the map is zero outside the cells. Degenerate cells are empty. *)
Fixpoint is_tagged_step_function (R : realType) (f : R -> R)
    (w : seq R) (v : R -> R) : Prop :=
  match w with
  | a :: r :: ((b :: _) as rest) =>
      exists u : R -> R, is_tagged_step_function f rest u /\
        forall x, v x=if a<x<=b then f r else u x
  | _ => forall x, v x=0
  end.

(** Source for [tagged_step_function_unique]: supporting uniqueness
    of the cellwise-defined approximation in Federer 2.9.24,
    p. 169. The recursive laws determine every point value,
    including the left endpoint and the exterior of the partition. *)
Lemma tagged_step_function_unique (R : realType) (f : R -> R) (w : seq R)
    (u v : R -> R) :
  is_tagged_step_function f w u -> is_tagged_step_function f w v -> u=v.
Proof.
have [n] := ubnP (size w).
elim: n w u v=> [//|n ih] [|a [|r [|b rest]]] u v hs /= hu hv;
  try by apply: funext=> x; rewrite (hu x) (hv x).
have [u' [hu' hU]] := hu; have [v' [hv' hV]] := hv.
have hsize : (size (b::rest)<n)%N by move: hs; rewrite /= !ltnS; exact: ltnW.
have he := ih (b::rest) u' v' hsize hu' hv'.
apply: funext=> x; by rewrite (hU x) (hV x) he.
Qed.
