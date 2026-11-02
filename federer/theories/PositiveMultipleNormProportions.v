(** Federer (1969), 2.4.15, p. 89: sufficiency of positive proportionality
    for the printed norm identities. This direction holds for every norm,
    and needs no inner product or completeness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MinkowskiEqualityUP PositiveProportionalityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_multiple_norm_proportions]: pointwise
    support for Federer 2.4.15, p. 89: if x=c y and
    c is nonnegative, the norm proportions are c/(c+1),1/(c+1).
    Homogeneity of the supplied norm proves the assertion. *)
Lemma positive_multiple_norm_proportions (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (c : R) (x y : V) :
  0 <= c -> x=c *: y ->
  N x=(c/(c+1))*N (x+y) /\ N y=(c+1)^-1*N (x+y).
Proof.
move=> hc hx.
have hc1 : 0 < c+1.
  have hh := lerD hc (lexx (1:R)); rewrite add0r in hh.
  exact: lt_le_trans ltr01 hh.
have hc0 : c+1 != 0 by rewrite gt_eqF.
have hs : x+y=(c+1) *: y by rewrite scalerDl scale1r hx.
have hsum : N (x+y)=(c+1)*N y.
  by rewrite hs (real_seminorm_scale hN.1) (ger0_norm (ltW hc1)).
split.
- by rewrite hsum hx (real_seminorm_scale hN.1) (ger0_norm hc) mulrA divfK.
- by rewrite hsum mulrA mulVf // mul1r.
Qed.

(** Source for [positive_multiple_minkowski_condition]: supporting
    almost-everywhere implication in Federer 2.4.15, p. 89.
    A single nonnegative multiple gives the global norm coefficients,
    with no measurability or integrability hypothesis needed here. *)
Lemma positive_multiple_minkowski_condition (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) (f g : partial_function X V) :
  0 <= c -> measure_almost_everywhere mu (partial_positive_multiple_locus c f g) ->
  is_minkowski_equality_condition N mu f g.
Proof.
move=> hc he.
have hc1 : 0 < c+1.
  have hh := lerD hc (lexx (1:R)); rewrite add0r in hh.
  exact: lt_le_trans ltr01 hh.
have hc0 : c+1 != 0 by rewrite gt_eqF.
exists (c/(c+1)),((c+1)^-1); split.
- exact: divr_ge0 hc (ltW hc1).
split; first by rewrite invr_ge0; exact: ltW hc1.
split; first by rewrite -[X in _+X]mul1r -mulrDl mulfV.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [u [v [hu [hv huv]]]]; exists u,v; split=> //; split=> //.
exact (@positive_multiple_norm_proportions R V N hN c u v hc huv).
Qed.

(** Source for [minkowski_condition_symmetric]: supporting symmetry
    of the printed condition in Federer 2.4.15, p. 89.
    Exchanging the functions exchanges their two norm coefficients. *)
Lemma minkowski_condition_symmetric (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X V) :
  is_minkowski_equality_condition N mu f g -> is_minkowski_equality_condition N mu g f.
Proof.
move=> [a [b [ha [hb [hab he]]]]]; exists b,a; split=> //; split=> //.
split; first by rewrite addrC.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [u [v [hu [hv [hnu hnv]]]]]; exists v,u; split=> //; split=> //.
by rewrite addrC.
Qed.

(** Source for [positive_proportionality_minkowski_condition]: sufficiency
    of the bracketed condition for the general criterion in Federer 2.4.15,
    p. 89 Both orientations, including the coefficient zero, are retained. *)
Theorem positive_proportionality_minkowski_condition (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X V) :
  measure_almost_positively_proportional mu f g -> is_minkowski_equality_condition N mu f g.
Proof.
move=> [c [hc [he|he]]].
- exact (@positive_multiple_minkowski_condition R X V N hN mu hm c f g hc he).
- apply: (@minkowski_condition_symmetric R X V N mu hm g f).
  exact (@positive_multiple_minkowski_condition R X V N hN mu hm c g f hc he).
Qed.
