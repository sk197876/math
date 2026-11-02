(** Federer (1969), proof of 2.8.7, p. 144: selected members have positive
    measure and the sum of their enlargement measures is at most lambda
    times the measure of the testing open set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureDisjointSupport
  NonnegativeSum NonnegativeSumScale CountablyClosedFamilyUP WeightedEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [strict_enlargement_bound_positive]: the assertion phi(S)>0
    in Federer 2.8.7, p. 144, following from the strict enlargement
    inequality This implication does not need a separate positive-weight or
    nonempty-set premise. *)
Lemma strict_enlargement_bound_positive (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (d : set X -> R) (tau lambda : R) (S : set X) :
  mu (weighted_enlargement F d tau S) < lambda%:E * mu S -> 0 < mu S.
Proof.
move=> hbound.
case: (eqVneq (mu S) 0)=> [hz|hn].
- have h := le_lt_trans (measure_nonnegative hm _) hbound.
  by rewrite hz mule0 ltxx in h.
- by rewrite lt_neqAle eq_sym hn (measure_nonnegative hm).
Qed.

(** Source for [enlargement_selection_sum_bound]: the displayed sum estimate
    in Federer 2.8.7, p. 144 Disjoint measurable members contained in W give
    sum phi(hat S)<=lambda phi(W). Countability and finiteness of phi(W) are
    not needed for this bound itself. *)
Lemma enlargement_selection_sum_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F G : set (set X)) (d : set X -> R) (tau lambda : R) (W : set X) :
  set_family_disjoint G ->
  (forall S, G S -> measure_measurable mu S) ->
  (forall S, G S -> S `<=` W) -> (0 <= lambda)%R ->
  (forall S, G S -> mu (weighted_enlargement F d tau S) <= lambda%:E * mu S) ->
  nonnegative_sum G (fun S => mu (weighted_enlargement F d tau S)) <= lambda%:E * mu W.
Proof.
move=> hdis hmeas hwithin hlambda hbound.
have hsum := @measure_disjoint_sum_bound R X [the choiceType of set X]
  mu hm W G idfun hwithin hmeas hdis.
apply: le_trans (@nonnegative_sum_mono R [the choiceType of set X] G
  (fun S => mu (weighted_enlargement F d tau S)) (fun S => lambda%:E * mu S) hbound) _.
rewrite (@nonnegative_sum_scale R [the choiceType of set X] G mu lambda hlambda
  (fun S _ => measure_nonnegative hm S)).
apply: lee_wpmul2l; first by rewrite lee_fin.
exact hsum.
Qed.
