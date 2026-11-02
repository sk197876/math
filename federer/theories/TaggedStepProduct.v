(** Federer (1969), 2.9.24, p. 169: the product of the step approximation
    with g' splits into its cell products. The following pointwise finite
    identity precedes integration. The local Federer erratum has no entry
    for this supporting identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import TaggedStepFunction TaggedStepBounds TotalScalarCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [tagged_step_first_cell_product]: supporting finite
    decomposition of f_n g' in Federer 2.9.24, p. 169.
    The remaining step map vanishes on the first cell, since
    its own first endpoint is b. This is pointwise, with
    no regularity or measurability assumption on either factor. *)
Lemma tagged_step_first_cell_product (R : realType) (f v : R -> R)
    (a r b : R) (rest : seq R) : sorted <=%O (a::r::b::rest) ->
  (fun x => tagged_step_function f (a::r::b::rest) x*v x)=
    (fun x => f r*total_scalar_cutoff (`]a,b] : set R) v x+
      tagged_step_function f (b::rest) x*v x).
Proof.
move=> /andP[_ /andP[_ htail]]; apply: funext=> x.
rewrite tagged_step_function_cons; case: ifP=> hx.
- have hI : (`]a,b] : set R) x by rewrite /= in_itv /=.
  have /andP[_ hxb] := hx.
  have hz := @tagged_step_function_outside R f (b::rest) htail x (or_introl hxb).
  by rewrite (total_scalar_cutoff_on v hI) hz mul0r addr0.
- have hI : ~ (`]a,b] : set R) x.
    rewrite /= in_itv /= => hh; by move: hx; rewrite hh.
  by rewrite (total_scalar_cutoff_off v hI) mulr0 add0r.
Qed.
