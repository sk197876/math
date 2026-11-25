(** Federer (1969), 2.6.6, p. 120: |gamma| is bounded by nu. The order-unit
    proof uses monotonicity and normalization; it applies before the
    continuous extension has been constructed. Source context and norm
    conventions: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import FunctionLatticeUP UniformFunctionNormUP VectorFunctionLattice FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalized_monotone_functional_uniform_bound]: the
    bound |gamma(f)|<=nu(f) in Federer 2.6.6, p. 120, from
    positivity, linearity and gamma(1) = 1. *)
Theorem normalized_monotone_functional_uniform_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_vector_function_lattice L -> L (fun _=>1) ->
  is_linear_functional_on_functions L A -> A (fun _=>1) = 1 ->
  (forall f g, L f -> L g -> function_le f g -> A f<=A g) ->
  forall f n, L f -> is_uniform_function_norm f n -> `|A f|<=n.
Proof.
move=> hL h1 hA hA1 hmono f n hf hn.
have hconst c : L (fun _ : X=>c) /\ A (fun _ : X=>c)=c.
  have he : (fun _ : X=>c*1)=(fun _ : X=>c) by apply: funext=> x; rewrite mulr1.
  split.
  - by have hh := hL.2.2 c _ h1; rewrite he in hh.
  - by have hh := hA.2 c _ h1; rewrite he hA1 mulr1 in hh.
have hup : function_le f (fun _=>n).
  move=> x; exact: le_trans (ler_norm (f x)) (uniform_function_norm_bound hn x).
have hlo : function_le (fun _=> -n) f.
  move=> x; have := uniform_function_norm_bound hn x; by rewrite ler_norml=> /andP[].
have hupper := hmono f _ hf (hconst n).1 hup.
have hlower := hmono _ f (hconst (-n)).1 hf hlo.
rewrite (hconst n).2 in hupper; rewrite (hconst (-n)).2 in hlower.
by rewrite ler_norml hlower hupper.
Qed.
