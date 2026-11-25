(** Federer (1969), 2.8.17, pp. 151–152: the function delta(S)+phi(hat
    S)/phi(S). The May 1987 erratum, p. 3, book p. 151 line 24, requires
    positivity of phi on V(X). Boundedness and the standing hypotheses also
    make these denominators finite. That change is not adopted here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic PartialFunctionUP
  WeightedEnlargements FamilyWeightedEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [family_enlargement_ratio_value]: the expression
    in the hypothesis of Federer 2.8.17, p. 151, with
    delta and S on their exact family domains. Division uses
    the reciprocal of the finite positive denominator, as ensured
    by the corrected theorem's hypotheses; other values of this
    auxiliary expression have no role in that theorem. *)
Definition family_enlargement_ratio_value (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (F : set (set X))
    (delta : {S : set X | F S} -> R) (tau : R) (S : {S : set X | F S}) :=
  (delta S)%:E + phi (family_weighted_enlargement delta tau S) * ((fine (phi (sval S)))^-1)%:E.

(** Source for [family_enlargement_ratio_function]: the partial
    function in the upper limit of Federer 2.8.17, p. 151.
    Its domain is exactly F, matching delta's domain; no
    extension outside the family changes the relation limit. *)
Definition family_enlargement_ratio_function (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (F : set (set X))
    (delta : {S : set X | F S} -> R) (tau : R) : partial_function (set X) (\bar R).
Proof.
refine (@Build_partial_function (set X) (\bar R) (fun S y =>
  exists T : {S : set X | F S}, sval T = S /\ family_enlargement_ratio_value phi delta tau T = y) _).
move=> S y z [[T hT] [hTS hy]] [[U hU] [hUS hz]].
have he : exist F T hT = exist F U hU by apply: eq_exist; exact: eq_trans hTS (esym hUS).
by move: hy; rewrite he hz=> ->.
Defined.

(** Source for [family_enlargement_ratio_graph]: supporting
    value rule for the function in Federer 2.8.17, p. 151.
    A proof of eligible membership suffices to exhibit its value. *)
Lemma family_enlargement_ratio_graph (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (F : set (set X))
    (delta : {S : set X | F S} -> R) (tau : R) (S : {S : set X | F S}) :
  partial_function_graph (family_enlargement_ratio_function phi delta tau) (sval S)
    (family_enlargement_ratio_value phi delta tau S).
Proof. by exists S. Qed.

(** Source for [family_enlargement_ratio_extension]: supporting
    agreement with a total weight representative in the proof
    of Federer 2.8.17, pp. 151–152. Both the enlargement
    and numerator depend only on the weight's values on F. *)
Lemma family_enlargement_ratio_extension (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (F : set (set X))
    (delta : {S : set X | F S} -> R) (d : set X -> R) (tau : R) :
  is_family_weight_extension delta d -> forall S,
  family_enlargement_ratio_value phi delta tau S =
    (d (sval S))%:E + phi (weighted_enlargement F d tau (sval S)) * ((fine (phi (sval S)))^-1)%:E.
Proof.
move=> hd [S hS]; rewrite /family_enlargement_ratio_value /= (hd S hS).
by rewrite (@family_weighted_enlargement_extension R X F delta d tau hd (exist F S hS)).
Qed.

(** Source for [nonnegative_enlargement_ratio_bound]: the
    two numerical consequences of the cutoff in Federer
    2.8.17, pp. 151–152: delta(S)<n and phi(hat S)<n phi(S).
    This scalar support requires the finite positive denominator
    added explicitly by the erratum, p. 3, book p. 151 line 24. *)
Lemma nonnegative_enlargement_ratio_bound (R : realType)
    (d q n : R) (a : \bar R) :
  (0 <= d)%R -> (0 < q)%R -> 0 <= a ->
  d%:E + a * (q^-1)%:E < n%:E ->
  (d < n)%R /\ a < n%:E * q%:E.
Proof.
move=> hd hq ha hb.
have hi : (0 < q^-1)%R by rewrite invr_gt0.
have hp : 0 <= a * (q^-1)%:E by apply: mule_ge0=> //; rewrite lee_fin; exact: ltW hi.
have hdE : 0 <= d%:E by rewrite lee_fin.
split.
- have hle : d%:E <= d%:E + a * (q^-1)%:E by apply: lee_paddr hp (lexx _).
  by have := le_lt_trans hle hb; rewrite lte_fin.
- have hle : a * (q^-1)%:E <= d%:E + a * (q^-1)%:E by apply: lee_paddl hdE (lexx _).
  have h := le_lt_trans hle hb.
  have hqE : 0 < q%:E by rewrite lte_fin.
  have hqf : q%:E \is a fin_num by [].
  by move: h; rewrite -(@lte_pmul2r R q%:E hqf hqE) -muleA -EFinM mulVf ?gt_eqF // mule1.
Qed.

(** Source for [weighted_enlargement_mono_family]: supporting
    comparison of the cut-down family's enlargement with the
    original enlargement in Federer 2.8.17, pp. 151–152.
    The same weight representative and tau are used on both. *)
Lemma weighted_enlargement_mono_family (R : realType) (X : choiceType)
    (F G : set (set X)) (d : set X -> R) tau S :
  F `<=` G -> weighted_enlargement F d tau S `<=` weighted_enlargement G d tau S.
Proof.
move=> hFG x [T [hT hrest] hx]; exists T=> //; split=> //; exact: hFG.
Qed.
