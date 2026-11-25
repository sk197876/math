(** Federer (1969), 2.4.15, p. 89: the complete bracketed inner-product
    equality criterion. it has no integration chapter. We assume only the
    inner-product and norm laws, without finite dimension or completeness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerProductUP InnerNormUP InnerNormProportions
  PartialFunctionUP PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PositiveProportionalityUP PositiveMultipleNormProportions MinkowskiEqualityUP
  MeasureMinkowskiEquality MeasureLpNorm MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inner_minkowski_condition_positive_proportionality]:
    necessity of the bracketed condition in Federer 2.4.15,
    p. 89, from its general norm identities. If the second
    norm coefficient is positive, the global vector coefficient is a/b;
    if it is zero, the second function is almost everywhere zero. *)
Theorem inner_minkowski_condition_positive_proportionality
    (R : realType) (X : choiceType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) (hBN : is_inner_norm B N)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X V) :
  is_minkowski_equality_condition N mu f g -> measure_almost_positively_proportional mu f g.
Proof.
move=> [a [b [ha [hb [hab he]]]]].
have [hb0|hb0] := eqVneq b 0%R.
- exists 0%R; split=> //; right.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [u [v [hu [hv [hnu hnv]]]]]; exists v,u; split=> //; split=> //.
  have hv0 : v=0%R by apply: hN.2; rewrite hnv hb0 mul0r.
  by rewrite hv0 scale0r.
have hbpos : (0 < b)%R by rewrite lt_neqAle eq_sym hb0 hb.
exists (a/b)%R; split; first exact: divr_ge0 ha hb.
left; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [u [v [hu [hv [hnu hnv]]]]]; exists u,v; split=> //; split=> //.
exact (@inner_norm_proportions_multiple R V B hB N hN hBN a b u v hbpos hab hnu hnv).
Qed.

(** Source for [minkowski_inner_equality_iff]: direct bracketed equivalence
    in Federer 2.4.15, p. 89 Equality in Minkowski's inequality holds
    exactly when the two functions are almost positively proportional, with
    a global coefficient and either orientation. *)
Theorem minkowski_inner_equality_iff
    (R : realType) (X : choiceType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) (hBN : is_inner_norm B N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> is_measure_lp_function mu p f -> is_measure_lp_function mu p g ->
  (measure_lp_norm mu N p (partial_vector_add f g) = measure_lp_norm mu N p f + measure_lp_norm mu N p g <->
   measure_almost_positively_proportional mu f g).
Proof.
move=> hp hf hg; split=> he.
- apply: (@inner_minkowski_condition_positive_proportionality R X V B hB N hN hBN mu hm f g).
  exact ((proj1 (@minkowski_equality_iff R X V N hN mu hm p f g hp hf hg)) he).
- apply: (proj2 (@minkowski_equality_iff R X V N hN mu hm p f g hp hf hg)).
  exact (@positive_proportionality_minkowski_condition R X V N hN mu hm f g he).
Qed.
