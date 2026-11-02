(** Federer (1969), 2.5.6, pp. 97–98: the positive and negative variations
    may be infinite under additivity alone, but one is finite exactly when
    the other is. The supremum and infimum below use the project's sealed
    extended-real bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP
  DaniellVariationUP LatticeAdditiveFunctional ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lattice_positive_variation]: positive supremum from Federer
    2.5.5, p. 96, used without a boundedness hypothesis in 2.5.6, pp. 97–98
    This definition permits positive infinity. *)
Definition lattice_positive_variation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (f : X -> R) :=
  extended_real_sup (daniell_interval_values L A f).

(** Source for [lattice_negative_variation]: negative infimum from Federer
    2.5.5, p. 96, used in 2.5.6, pp. 97–98 *)
Definition lattice_negative_variation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (f : X -> R) :=
  - extended_real_inf (daniell_interval_values L A f).

(** Source for [lattice_negative_variation_dual]: order-dual expression
    supporting Federer 2.5.6, pp. 97–98 No additivity is needed. *)
Lemma lattice_negative_variation_dual (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (f : X -> R) :
  lattice_negative_variation L A f =
  lattice_positive_variation L (fun k => (- A k)%R) f.
Proof.
rewrite /lattice_negative_variation /lattice_positive_variation.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite leeNl; apply: extended_real_inf_greatest=> v [k [hk ->]].
  rewrite leeNl; apply: extended_real_sup_upper; by exists k.
- apply: extended_real_sup_least=> v [k [hk ->]].
  change (is_true (- (A k)%:E <= - extended_real_inf (daniell_interval_values L A f))).
  rewrite leeN2; apply: extended_real_inf_lower; by exists k.
Qed.

(** Source for [lattice_positive_variation_nonnegative]: zero belongs to
    each positive order interval, supporting the finiteness assertion of
    Federer 2.5.6, pp. 97–98 *)
Lemma lattice_positive_variation_nonnegative (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_lattice_additive_functional L A) f :
  positive_function_lattice L f -> 0 <= lattice_positive_variation L A f.
Proof.
move=> [hf hf0]; apply: extended_real_sup_upper.
exists (fun _ => 0%R); split.
- split; first exact: (@function_lattice_zero R X L hL f hf).
  split; first by move=> x; exact: lexx.
  exact: hf0.
- by rewrite (@lattice_additive_zero R X L A hL hA f hf).
Qed.

(** Source for [lattice_positive_variation_finite_bound]: finite supremum is
    equivalent to a real upper bound, the order step in Federer 2.5.6, pp.
    97–98 Nonnegativity excludes negative infinity. *)
Lemma lattice_positive_variation_finite_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_lattice_additive_functional L A) f :
  positive_function_lattice L f ->
  (lattice_positive_variation L A f < +oo <->
   exists b : R, forall k, lattice_positive_order_interval L f k -> (A k <= b)%R).
Proof.
move=> hf; split.
- move=> ht.
  have h0 := @lattice_positive_variation_nonnegative R X L A hL hA f hf.
  have hs : lattice_positive_variation L A f \is a fin_num.
    rewrite fin_numElt; apply/andP; split=> //.
    exact: lt_le_trans (ltNyr (0%R : R)) h0.
  exists (fine (lattice_positive_variation L A f))=> k hk.
  have hu : (A k)%:E <= lattice_positive_variation L A f.
    apply: extended_real_sup_upper; by exists k.
  rewrite -(fineK hs) lee_fin in hu; exact: hu.
- move=> [b hb].
  have hu : lattice_positive_variation L A f <= b%:E.
    apply: extended_real_sup_least=> v [k [hk ->]].
    rewrite lee_fin; exact: hb k hk.
  exact: le_lt_trans hu (ltry b).
Qed.

(** Source for [lattice_variations_finite_iff]: direct formalisation of the
    equivalence in Federer 2.5.6, pp. 97–98 Only additivity and lattice
    closure are assumed, so both variations may be infinite. *)
Theorem lattice_variations_finite_iff (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_lattice_additive_functional L A) f :
  positive_function_lattice L f ->
  (lattice_positive_variation L A f < +oo <-> lattice_negative_variation L A f < +oo).
Proof.
move=> hf; rewrite lattice_negative_variation_dual.
have hn := @lattice_additive_negation R X L A hA.
rewrite (@lattice_positive_variation_finite_bound R X L A hL hA f hf).
rewrite (@lattice_positive_variation_finite_bound R X L (fun k => (- A k)%R) hL hn f hf).
exact: (@lattice_additive_two_sided_order_bounded_iff R X L A hL hA f hf.1).
Qed.
