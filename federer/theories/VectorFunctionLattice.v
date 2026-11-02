(** Federer (1969), 2.5.6, p. 98: the additional hypothesis that L is a
    vector space in the variation formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP LatticeAdditiveFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_vector_function_lattice]: axiomatic vector-space
    qualification in Federer 2.5.6, p. 98 Addition is already a lattice law;
    zero and closure under all real scalars are specified here. *)
Definition is_vector_function_lattice (R : realType) (X : Type) (L : set (X -> R)) :=
  is_function_lattice L /\ L (fun _ => 0) /\
  forall c f, L f -> L (fun x => c * f x).

(** Source for [vector_function_lattice_negation]: vector-space closure
    supporting the formula in Federer 2.5.6, p. 98 *)
Lemma vector_function_lattice_negation (R : realType) (X : Type) (L : set (X -> R)) :
  is_vector_function_lattice L -> forall f, L f -> L (fun x => - f x).
Proof.
move=> hL f hf; have hh := hL.2.2 (-1) f hf.
have he : (fun x => -1 * f x)=(fun x => - f x) by apply: funext=> x; rewrite mulN1r.
by rewrite he in hh.
Qed.

(** Source for [vector_function_lattice_difference]: arbitrary subtraction
    under the vector-space hypothesis of Federer 2.5.6, p. 98 *)
Lemma vector_function_lattice_difference (R : realType) (X : Type) (L : set (X -> R)) :
  is_vector_function_lattice L -> forall f g, L f -> L g -> L (fun x => f x-g x).
Proof.
move=> hL f g hf hg; apply: (@function_lattice_add R X L hL.1 f (fun x => - g x) hf).
exact: (@vector_function_lattice_negation R X L hL g hg).
Qed.

(** Source for [vector_lattice_additive_negation]: additivity gives
    mu(-g)=-mu(g), supporting the equivalence of the absolute value formula
    in Federer 2.5.6, p. 98, and the unsigned supremum. *)
Lemma vector_lattice_additive_negation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_lattice_additive_functional L A) f :
  L f -> A (fun x => - f x)= - A f.
Proof.
move=> hf; have hn := @vector_function_lattice_negation R X L hL f hf.
have ha := hA f _ hf hn.
have he : (fun x => f x + - f x)=(fun _ : X => 0) by apply: funext=> x; rewrite subrr.
rewrite he (@lattice_additive_zero R X L A hL.1 hA f hf) in ha.
have hh := congr1 (fun r => r-A f) ha.
by rewrite sub0r addrAC subrr add0r in hh.
Qed.

(** Source for [vector_lattice_additive_difference]: additive evaluation of
    differences used in the supremum formula in Federer 2.5.6, p. 98 *)
Lemma vector_lattice_additive_difference (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_lattice_additive_functional L A) f g :
  L f -> L g -> A (fun x => f x-g x)=A f-A g.
Proof.
move=> hf hg; rewrite (hA f (fun x => - g x) hf (@vector_function_lattice_negation R X L hL g hg)).
by rewrite (@vector_lattice_additive_negation R X L A hL hA g hg).
Qed.

(** Source for [lattice_symmetric_order_interval]: admissible functions |g|
    <= f in the variation formula of Federer 2.5.6, p. 98 *)
Definition lattice_symmetric_order_interval (R : realType) (X : Type)
    (L : set (X -> R)) (f : X -> R) :=
  [set g | L g /\ forall x, `|g x| <= f x].

(** Source for [lattice_interval_difference_symmetric]: the difference of
    two members of [0,f] lies in [-f,f], supporting the lower supremum bound
    in Federer 2.5.6, p. 98 *)
Lemma lattice_interval_difference_symmetric (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_vector_function_lattice L) f k l :
  lattice_positive_order_interval L f k -> lattice_positive_order_interval L f l ->
  lattice_symmetric_order_interval L f (fun x => k x-l x).
Proof.
move=> hk hl; split; first exact: (@vector_function_lattice_difference R X L hL k l hk.1 hl.1).
move=> x; rewrite ler_norml; apply/andP; split.
- rewrite -[k x-l x]opprB lerN2.
  apply: le_trans (hl.2.2 x).
  by rewrite gerBl; exact: hk.2.1.
- apply: le_trans (hk.2.2 x).
  by rewrite gerBl; exact: hl.2.1.
Qed.
