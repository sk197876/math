(** Federer (1969), 2.5.6, pp. 97–98: additivity alone suffices for the
    finiteness equivalence of the two variations. These laws deliberately do
    not assume order boundedness, positive homogeneity of the functional,
    monotonicity, or increasing continuity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellIntegralAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_lattice_additive_functional]: exact additivity hypothesis
    isolated in Federer 2.5.6, p. 97 *)
Definition is_lattice_additive_functional (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :=
  forall f g, L f -> L g -> A (fun x => f x+g x)=A f+A g.

(** Source for [lattice_additive_zero]: zero value from additivity alone,
    supporting Federer 2.5.6, pp. 97–98 A member is needed to obtain zero in
    the possibly empty lattice. *)
Lemma lattice_additive_zero (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_lattice_additive_functional L A) (f : X -> R) :
  L f -> A (fun _ => 0)=0.
Proof.
move=> hf; have hz := @function_lattice_zero R X L hL f hf.
have ha := hA _ _ hz hz.
have he : (fun _ : X => 0+0)=(fun _ => (0 : R)) by apply: funext=> x; rewrite add0r.
rewrite he in ha.
have hh := congr1 (fun r => r-A (fun _ => 0)) ha.
rewrite subrr addrK in hh; exact: esym hh.
Qed.

(** Source for [lattice_additive_ordered_difference]: the reflection k maps
    to f-k underlying Federer 2.5.6, pp. 97–98 *)
Lemma lattice_additive_ordered_difference (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_lattice_additive_functional L A) (f k : X -> R) :
  L f -> lattice_positive_order_interval L f k -> A (fun x => f x-k x)=A f-A k.
Proof.
move=> hf hk.
have hd := @lattice_positive_order_interval_complement R X L hL f k hf hk.
have ha := hA k _ hk.1 hd.1.
have he : (fun x => k x+(f x-k x))=f by apply: funext=> x; rewrite addrCA subrr addr0.
rewrite he in ha; by rewrite ha addrAC subrr add0r.
Qed.

(** Source for [lattice_additive_negation]: -mu remains additive in the
    symmetric finiteness argument of Federer 2.5.6, pp. 97–98 *)
Lemma lattice_additive_negation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_lattice_additive_functional L A -> is_lattice_additive_functional L (fun f => - A f).
Proof. move=> hA f g hf hg; by rewrite (hA f g hf hg) opprD. Qed.

(** Source for [lattice_additive_negative_order_bound]: explicit upper-bound
    transfer in Federer 2.5.6, pp. 97–98 This uses additivity and lattice
    closure only, not the full Daniell hypotheses. *)
Lemma lattice_additive_negative_order_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_lattice_additive_functional L A) (f : X -> R) b :
  L f -> (forall k, lattice_positive_order_interval L f k -> A k <= b) ->
  forall k, lattice_positive_order_interval L f k -> - A k <= b-A f.
Proof.
move=> hf hb k hk.
have hd := @lattice_positive_order_interval_complement R X L hL f k hf hk.
have hv := hb _ hd.
rewrite (@lattice_additive_ordered_difference R X L A hL hA f k hf hk) in hv.
by rewrite lerBrDr addrC.
Qed.

(** Source for [lattice_additive_two_sided_order_bounded_iff]: supporting
    bound formulation of the finiteness equivalence in Federer 2.5.6, pp.
    97–98 Empty admissible intervals are included. *)
Lemma lattice_additive_two_sided_order_bounded_iff (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_lattice_additive_functional L A) (f : X -> R) :
  L f ->
  (exists b : R, forall k, lattice_positive_order_interval L f k -> A k <= b) <->
  (exists b : R, forall k, lattice_positive_order_interval L f k -> - A k <= b).
Proof.
move=> hf; split; move=> [b hb].
- exists (b-A f); exact: (@lattice_additive_negative_order_bound R X L A hL hA f b hf hb).
- exists (b+A f)=> k hk.
  have hh := @lattice_additive_negative_order_bound R X L (fun k => - A k) hL
    (@lattice_additive_negation R X L A hA) f b hf hb k hk.
  by rewrite opprK opprK in hh.
Qed.
