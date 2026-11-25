(** Federer (1969), 2.5.7, p. 98: the positive variation of the bounded
    functional satisfies mu+(f)<=M phi_(p)(f) on L+. We use only the
    abstract variation supremum law from 2.5.5, p. 96. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP DaniellIntegralUP DaniellVariationUP
  DaniellVariationBounds TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalScalarLpFunctionalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_positive_variation_norm_bound]: direct preliminary bound
    in Federer 2.5.7, p. 98 It holds for every variation satisfying the
    defining supremum law, independently of its construction. *)
Lemma lp_positive_variation_norm_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p
    (A P : (X -> R) -> R) (M : R) :
  (0 <= M)%R ->
  (forall f, total_scalar_lp mu p f -> (`|A f| <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  is_daniell_positive_variation (total_scalar_lp mu p) A P ->
  forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R.
Proof.
move=> hM hb hP f hf.
apply: (@daniell_positive_variation_least R X (total_scalar_lp mu p) A P hP f _ hf).
exact: (@total_scalar_lp_functional_order_bound R X mu hm p A M hM hb f hf.1).
Qed.

(** Source for [lp_positive_variation_zero_norm]: the implication
    phi_(p)(h)=0 => mu+(h)=0 in the maximality contradiction of Federer
    2.5.7, p. 99 The positive function h must still belong to Lp. *)
Lemma lp_positive_variation_zero_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p
    (A P : (X -> R) -> R) (M : R) :
  (0 <= M)%R ->
  (forall f, total_scalar_lp mu p f -> (`|A f| <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  is_daniell_positive_variation (total_scalar_lp mu p) A P ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f -> (0 <= P f)%R) ->
  forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    total_scalar_lp_norm mu p f=0 -> P f=0%R.
Proof.
move=> hM hb hP hP0 f hf hz.
have hh := @lp_positive_variation_norm_bound R X mu hm p A P M hM hb hP f hf.
rewrite /finite_total_scalar_lp_norm hz /= mulr0 in hh.
apply/eqP; by rewrite eq_le hh hP0.
Qed.
