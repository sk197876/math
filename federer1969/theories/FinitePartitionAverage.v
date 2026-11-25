(** Federer (1969), 2.3.8, p. 79, displayed finite average f=sum_j n^(-1)(n
    s_j f). Source context: MeasurableNormedFunctionUP.v. The representation
    is purely algebraic and pointwise, and so can also be applied on the
    domain of a partial function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import CharacteristicFunctionUP CharacteristicVectorPiece.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_partition_average_pointwise]: direct finite
    average identity of Federer 2.3.8, p. 79. There
    are n>0 disjoint pieces covering the source, each with its
    abstract characteristic scalar. *)
Lemma finite_partition_average_pointwise (R : realType) (X : Type) (V : lmodType R)
    n (S : 'I_n -> set X) (s : 'I_n -> X -> R) (f : X -> V) :
  (0 < n)%N -> (forall i, is_characteristic_function (S i) (s i)) ->
  (forall x, exists i, S i x) -> (forall i j x, S i x -> S j x -> i=j) ->
  forall x, f x = \sum_(i < n) n%:R^-1 *:
    characteristic_vector_piece (s i) (fun z => n%:R *: f z) x.
Proof.
move=> hn hs hcover hdis x; have [k hk] := hcover x.
rewrite (bigD1 k) //=.
have hzero : \sum_(i < n | i != k) n%:R^-1 *:
    characteristic_vector_piece (s i) (fun z => n%:R *: f z) x = 0.
  apply: big1=> i hik.
  have hnSi : ~ S i x.
    move=> hi; have e := hdis i k x hi hk; by move: hik; rewrite e eqxx.
  by rewrite /characteristic_vector_piece (characteristic_off_set (hs i) hnSi) scale0r scaler0.
rewrite hzero addr0 /characteristic_vector_piece (characteristic_on_set (hs k) hk)
  scale1r scalerA mulVf ?scale1r //.
by rewrite pnatr_eq0 -lt0n.
Qed.

(** Source for [finite_partition_average_function]: function-space
    form of the displayed representation in Federer 2.3.8,
    p. 79. Pointwise function algebra is the general set-
    theoretic background already used in Chapter 1. *)
Lemma finite_partition_average_function (R : realType) (X : Type) (V : lmodType R)
    n (S : 'I_n -> set X) (s : 'I_n -> X -> R) (f : X -> V) :
  (0 < n)%N -> (forall i, is_characteristic_function (S i) (s i)) ->
  (forall x, exists i, S i x) -> (forall i j x, S i x -> S j x -> i=j) ->
  f = \sum_(i < n) n%:R^-1 *: characteristic_vector_piece (s i) (fun z => n%:R *: f z).
Proof.
move=> hn hs hc hd; rewrite fct_sumE; apply: funext=> x.
exact (@finite_partition_average_pointwise R X V n S s f hn hs hc hd x).
Qed.

(** Source for [finite_average_nonnegative_weights]: the positive
    equal weights in Federer 2.3.8, p. 79, supporting
    the claimed convex-combination representation. *)
Lemma finite_average_nonnegative_weights (R : realType) n : 0 <= (n%:R : R)^-1.
Proof. by rewrite invr_ge0 ler0n. Qed.

(** Source for [finite_average_weights_sum]: normalization of
    the equal weights in Federer 2.3.8, p. 79;
    n>0 is the positive finite-partition convention. *)
Lemma finite_average_weights_sum (R : realType) n : (0 < n)%N ->
  \sum_(i < n) (n%:R : R)^-1 = 1.
Proof.
move=> hn; rewrite sumr_const card_ord -(mulr_natr ((n%:R : R)^-1) n).
rewrite mulVf //.
by rewrite pnatr_eq0 -lt0n.
Qed.
