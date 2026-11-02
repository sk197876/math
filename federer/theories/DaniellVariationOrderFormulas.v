(** Federer (1969), 2.5.5, p. 96: the displayed supremum and
    negative-infimum formulas for the variations. The abstract
    negative-variation specification uses the equivalent supremum of -mu;
    these lemmas explicitly recover the book's two formulas with the
    project's sealed bounds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellVariationUP
  ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_positive_variation_supremum_formula]: exact first
    defining formula in Federer 2.5.5, p. 96 *)
Lemma daniell_positive_variation_supremum_formula (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hP : is_daniell_positive_variation L A P) (f : X -> R) :
  positive_function_lattice L f ->
  (P f)%:E=extended_real_sup (daniell_interval_values L A f).
Proof.
move=> hf; apply: (extended_real_supremum_unique (hP f hf)); constructor.
- exact: extended_real_sup_upper.
- exact: extended_real_sup_least.
Qed.

(** Source for [daniell_negative_variation_infimum_formula]: exact second
    defining formula in Federer 2.5.5, p. 96 Order duality is proved from
    both bound laws, so the dual supremum does not hide a change to the
    displayed definition. *)
Lemma daniell_negative_variation_infimum_formula (R : realType) (X : Type)
    (L : set (X -> R)) (A Q : (X -> R) -> R)
    (hQ : is_daniell_negative_variation L A Q) (f : X -> R) :
  positive_function_lattice L f ->
  (Q f)%:E= - extended_real_inf (daniell_interval_values L A f).
Proof.
move=> hf.
have he : extended_real_inf (daniell_interval_values L A f)= -(Q f)%:E.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite leeNr; apply: (extended_real_supremum_least (hQ f hf))=> v [k [hk ->]].
    change (is_true (- (A k)%:E <= - extended_real_inf (daniell_interval_values L A f))).
    rewrite leeN2; apply: extended_real_inf_lower; by exists k.
  - apply: extended_real_inf_greatest=> v [k [hk ->]].
    rewrite leeNl; apply: (extended_real_supremum_upper (hQ f hf)); by exists k.
by rewrite he oppeK.
Qed.
