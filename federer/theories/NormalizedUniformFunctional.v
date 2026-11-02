(** Federer (1969), 2.6.6, p. 120: the normalized norm-one
    extension is monotone. The argument below spells out the
    supporting order-unit observation: a linear functional bounded
    by the uniform norm and taking 1 to 1 is positive. Source
    editions and norm conventions: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import FunctionLatticeUP UniformFunctionNormUP VectorFunctionLattice FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalized_uniform_functional_positive]: supporting
    positivity of the infinite-product functional in Federer 2.6.6,
    p. 120, from its norm bound and its value on the constant 1. *)
Lemma normalized_uniform_functional_positive (R : realType) (X : Type)
    (L : set (X -> R)) (N A : (X -> R) -> R) :
  is_vector_function_lattice L -> L (fun _=>1) ->
  (forall f, L f -> is_uniform_function_norm f (N f)) ->
  is_linear_functional_on_functions L A -> A (fun _=>1) = 1 ->
  (forall f, L f -> `|A f|<=N f) ->
  forall f, L f -> (forall x, 0<=f x) -> 0<=A f.
Proof.
move=> hL h1 hN hA hA1 hb f hf hf0.
pose c := N f.
have hc : 0<=c := uniform_function_norm_nonnegative (hN f hf).
have hconst : L (fun _ : X=>c).
  have hh := hL.2.2 c _ h1.
  have he : (fun _ : X=>c*1)=(fun _ : X=>c) by apply: funext=> x; rewrite mulr1.
  by rewrite he in hh.
have hval : A (fun _ : X=>c)=c.
  have hh := hA.2 c _ h1.
  have he : (fun _ : X=>c*1)=(fun _ : X=>c) by apply: funext=> x; rewrite mulr1.
  by rewrite he hA1 mulr1 in hh.
have hd := @vector_function_lattice_difference R X L hL _ f hconst hf.
have hn : N (fun x=>c-f x)<=c.
  apply: (@uniform_function_norm_least R X _ _ (hN _ hd) c hc)=> x.
  rewrite ler_norml; apply/andP; split.
  - have hfc := le_trans (ler_norm (f x)) (uniform_function_norm_bound (hN f hf) x); change (is_true (f x<=c)) in hfc; lra.
  - have := hf0 x; lra.
have hbound := le_trans (ler_norm (A (fun x=>c-f x))) (le_trans (hb _ hd) hn).
rewrite (@vector_lattice_additive_difference R X L A hL hA.1 _ f hconst hf) hval in hbound.
lra.
Qed.

(** Source for [normalized_uniform_functional_monotone]: monotonicity
    of the extension in Federer 2.6.6, p. 120. It follows from
    positivity and the vector-space difference law. *)
Theorem normalized_uniform_functional_monotone (R : realType) (X : Type)
    (L : set (X -> R)) (N A : (X -> R) -> R) :
  is_vector_function_lattice L -> L (fun _=>1) ->
  (forall f, L f -> is_uniform_function_norm f (N f)) ->
  is_linear_functional_on_functions L A -> A (fun _=>1) = 1 ->
  (forall f, L f -> `|A f|<=N f) ->
  forall f g, L f -> L g -> function_le f g -> A f<=A g.
Proof.
move=> hL h1 hN hA hA1 hb f g hf hg hfg.
have hd := @vector_function_lattice_difference R X L hL g f hg hf.
have hpos : forall x, 0<=g x-f x by move=> x; rewrite subr_ge0; exact: hfg.
have hh := @normalized_uniform_functional_positive R X L N A hL h1 hN hA hA1 hb _ hd hpos.
by rewrite (@vector_lattice_additive_difference R X L A hL hA.1 g f hg hf) subr_ge0 in hh.
Qed.
