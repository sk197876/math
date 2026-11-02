(** Federer (1969), 2.4.15, p. 89: interpreting equality of the normalised
    powers from the two Holder applications. The supporting graph extraction
    preserves the original common domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic PartialNormPower RealPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalised_norm_power_equal_values]: supporting
    extraction of the normalised scalar norm equality in
    Federer 2.4.15, p. 89. Positive denominators
    have positive inverses, so their norm factors are the
    ordinary reciprocal scalars. *)
Lemma normalised_norm_power_equal_values (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b : R)
    (f : partial_function X V) (g : partial_function X W) :
  0 < a -> 0 < b ->
  measure_almost_equal mu (partial_norm_power N p (partial_vector_scale a^-1 f))
    (partial_norm_power M q (partial_vector_scale b^-1 g)) ->
  measure_almost_everywhere mu [set x | exists u v,
    partial_function_graph f x u /\ partial_function_graph g x v /\
    real_power (a^-1*N u) p = real_power (b^-1*M v) q].
Proof.
move=> ha hb he.
have hai : 0 <= a^-1 by rewrite invr_ge0; exact: ltW ha.
have hbi : 0 <= b^-1 by rewrite invr_ge0; exact: ltW hb.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [z [[u' [[u [hu huu]] huz]] [v' [[v [hv hvv]] hvz]]]].
rewrite -huu (real_seminorm_scale hN.1) (ger0_norm hai) in huz.
rewrite -hvv (real_seminorm_scale hM.1) (ger0_norm hbi) in hvz.
have heE : (real_power (a^-1*N u) p)%:E = (real_power (b^-1*M v) q)%:E by rewrite huz hvz.
exists u,v; split=> //; split=> //; exact (EFin_inj heE).
Qed.
