(** Federer (1969), 2.5.6, p. 98: variation as the supremum of absolute
    functional values on the symmetric order interval. The proof below
    includes infinite variations under additivity alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP
  DaniellVariationUP LatticeAdditiveFunctional LatticeExtendedVariation VectorFunctionLattice
  VectorVariationFiniteBounds ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [symmetric_functional_absolute_values]: exact set in the
    displayed formula of Federer 2.5.6, p. 98. *)
Definition symmetric_functional_absolute_values (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (f : X -> R) :=
  [set v : \bar R | exists g, lattice_symmetric_order_interval L f g /\ v=(`|A g|)%:E].

(** Source for [positive_interval_symmetric]: inclusion of [0,f] in the
    interval |g| <= f, supporting Federer 2.5.6, p. 98 *)
Lemma positive_interval_symmetric (R : realType) (X : Type)
    (L : set (X -> R)) f g :
  lattice_positive_order_interval L f g -> lattice_symmetric_order_interval L f g.
Proof. move=> [hg [hg0 hgf]]; split=> // x; by rewrite ger0_norm //; exact: hgf. Qed.

(** Source for [symmetric_absolute_supremum_dominates_variations]: each
    variation is bounded by the absolute supremum, supporting the infinite
    case of Federer 2.5.6, p. 98 *)
Lemma symmetric_absolute_supremum_dominates_variations (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) f :
  lattice_positive_variation L A f <= extended_real_sup (symmetric_functional_absolute_values L A f) /\
  lattice_negative_variation L A f <= extended_real_sup (symmetric_functional_absolute_values L A f).
Proof.
split; last rewrite lattice_negative_variation_dual;
  apply: extended_real_sup_least=> v [k [hk ->]].
- apply: le_trans (_ : (`|A k|)%:E <= _).
  + rewrite lee_fin; exact: ler_norm.
  + apply: extended_real_sup_upper; exists k; split=> //.
    exact: (@positive_interval_symmetric R X L f k hk).
- apply: le_trans (_ : (`|A k|)%:E <= _).
  + rewrite lee_fin; have hh := ler_norm (- A k)%R; by rewrite normrN in hh.
  + apply: extended_real_sup_upper; exists k; split=> //.
    exact: (@positive_interval_symmetric R X L f k hk).
Qed.

(** Source for [finite_variation_sum_supremum_laws]: both supremum laws for
    the finite case of Federer 2.5.6, p. 98 Empty X is allowed. *)
Lemma finite_variation_sum_supremum_laws (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_lattice_additive_functional L A) f p q :
  positive_function_lattice L f ->
  is_extended_real_supremum (daniell_interval_values L A f) p%:E ->
  is_extended_real_supremum (daniell_interval_values L (fun k => (- A k)%R) f) q%:E ->
  is_extended_real_supremum (symmetric_functional_absolute_values L A f) (p+q)%:E.
Proof.
move=> hf hp hq; constructor.
- move=> v [g [hg ->]]; rewrite lee_fin.
  exact: (@finite_variation_sum_upper R X L A hL hA f p q hf hp hq g hg).
- move=> d hd; case: d hd=> [b| |] hd; last first.
  + have hz : lattice_symmetric_order_interval L f (fun _ => 0%R).
      split; first exact: hL.2.1.
      by move=> x; rewrite normr0; exact: hf.2.
    have hh := hd _ (ex_intro _ (fun _ => 0%R) (conj hz erefl)).
    by rewrite leeNy_eq in hh.
  + exact: leey.
  + rewrite lee_fin; apply: (@finite_variation_sum_least R X L A hL hA f p q b hp hq)=> g hg.
    have hh := hd _ (ex_intro _ g (conj hg erefl)).
    by rewrite lee_fin in hh.
Qed.

(** Source for [lattice_variation_absolute_supremum]: exact formula in
    Federer 2.5.6, p. 98, including infinite variations. *)
Theorem lattice_variation_absolute_supremum (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_lattice_additive_functional L A) f :
  positive_function_lattice L f ->
  lattice_positive_variation L A f + lattice_negative_variation L A f =
  extended_real_sup (symmetric_functional_absolute_values L A f).
Proof.
move=> hf.
have hp0 := @lattice_positive_variation_nonnegative R X L A hL.1 hA f hf.
have hq0 : 0 <= lattice_negative_variation L A f.
  rewrite lattice_negative_variation_dual.
  exact: (@lattice_positive_variation_nonnegative R X L (fun k => (- A k)%R)
    hL.1 (@lattice_additive_negation R X L A hA) f hf).
have [hpu hqu] := @symmetric_absolute_supremum_dominates_variations R X L A f.
case Ep: (lattice_positive_variation L A f) hp0 hpu=> [p| |] hp0 hpu; last by [].
- case Eq: (lattice_negative_variation L A f) hq0 hqu=> [q| |] hq0 hqu; last by [].
  + have hp : is_extended_real_supremum (daniell_interval_values L A f) p%:E.
      rewrite -Ep; constructor; [exact: extended_real_sup_upper|exact: extended_real_sup_least].
    have hq : is_extended_real_supremum (daniell_interval_values L (fun k => (- A k)%R) f) q%:E.
      rewrite -Eq lattice_negative_variation_dual; constructor;
        [exact: extended_real_sup_upper|exact: extended_real_sup_least].
    apply: (extended_real_supremum_unique (@finite_variation_sum_supremum_laws R X L A hL hA f p q hf hp hq)).
    constructor; [exact: extended_real_sup_upper|exact: extended_real_sup_least].
  + rewrite addey //; apply/eqP; rewrite eq_le leey andbT; exact: hqu.
- have hn : lattice_negative_variation L A f != -oo.
    apply/eqP=> he; by rewrite he in hq0.
  rewrite addye //; apply/eqP; rewrite eq_le leey andbT; exact: hpu.
Qed.
