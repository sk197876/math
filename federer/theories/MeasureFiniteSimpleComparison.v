(** Federer (1969), proof of 2.4.6, p. 84: the finite disjoint test sum is
    bounded by each sufficiently late sequence function. Source context:
    ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  PartialExtendedOrderLoci MeasureStepIntegralIdentification MeasureIntegralUP
  MeasureIntegralComparison MeasureFiniteCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_disjoint_characteristic_bound]: supporting
    pointwise bound for the disjoint simple test sum in Federer
    2.4.6, p. 84; at most one term is nonzero. *)
Lemma finite_disjoint_characteristic_bound (R : realType) (X : Type) (I : choiceType)
    (C : {fset I}) (A : I -> set X) (s : I -> X -> R) (c : I -> R) x z :
  (forall i, i \in C -> is_characteristic_function (A i) (s i)) ->
  (forall i j, i \in C -> j \in C -> i != j -> forall x, A i x -> A j x -> False) ->
  0 <= z -> (forall i, i \in C -> A i x -> (c i)%:E <= z) ->
  (\sum_(i <- C) c i*s i x)%:E <= z.
Proof.
move=> hs hd hz hc; have [he|he] := pselect (exists i, i \in C /\ A i x).
- have [i [hi hix]] := he.
  have hzero : (\sum_(j <- (C `\ i)%fset) c j*s j x)%R = 0%R.
    rewrite big_seq; apply: big1=> j; rewrite !inE=> /andP[hji hj].
    have hjx : ~ A j x by move=> hx; exact: hd j i hj hi hji x hx hix.
    by rewrite (characteristic_off_set (hs j hj) hjx) mulr0.
  rewrite (big_fsetD1 _ hi) /= hzero addr0 (characteristic_on_set (hs i hi) hix) mulr1.
  exact: hc i hi hix.
- have hzero : (\sum_(i <- C) c i*s i x)%R = 0%R.
    rewrite big_seq; apply: big1=> i hi.
    have hn : ~ A i x by move=> hx; apply: he; exists i; split.
    by rewrite (characteristic_off_set (hs i hi) hn) mulr0.
  by rewrite hzero.
Qed.

(** Source for [measure_finite_simple_lower_bound]: supporting integral
    inequality for the finite simple test sum in Federer 2.4.6, p. 84 *)
Lemma measure_finite_simple_lower_bound (R : realType) (X I : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (C : {fset I})
    (A : I -> set X) (c : I -> R) (f : partial_function X (extended_real_line R)) a :
  (forall i, i \in C -> measure_measurable mu (A i)) ->
  (forall i j, i \in C -> j \in C -> i != j -> forall x, A i x -> A j x -> False) ->
  (forall i, i \in C -> (0 < c i)%R) ->
  (forall i, i \in C -> forall x, A i x ->
    exists z, partial_function_graph f x z /\ (c i)%:E <= z) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  is_measure_integral mu f a -> (\sum_(i <- C) (c i)%:E*mu (A i)) <= a.
Proof.
move=> hA hd hc hf hp hi.
pose s i : X -> real_line_metric R := @CharacteristicFunction.value R X (A i).
have hs i : is_characteristic_function (A i) (s i) := @CharacteristicFunction.laws R X (A i).
have hu := @measure_finite_positive_characteristic_integral R X I mu hm C A s c
  (fun i _ => hs i) hA hc.
apply: (@measure_integral_monotone R X mu hm _ f _ a hu hi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp)=> x [z [hz hz0]].
exists (\sum_(i <- C) c i*s i x)%:E, z; split; first by eexists; split; reflexivity.
split=> //; apply: (@finite_disjoint_characteristic_bound R X I C A s c x z
  (fun i _ => hs i) hd hz0)=> i hii hix.
have [w [hw hcw]] := hf i hii x hix.
have ew := partial_function_single_valued hw hz; by rewrite -ew.
Qed.
