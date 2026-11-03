(** Federer (1969), 3.2.41, printed p. 277, the definition immediately
    after the Brunn--Minkowski inequality: A+B consists of all x+y with
    x in A and y in B. Specify this as the least set containing all
    original pair sums. Existence and opaque selection are separate.
    The supporting algebra permits any additive abelian group and empty
    factors; the numbered measure theorem requires nonempty factors. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_vector_set_sum]: direct definition of A+B in
    Federer 3.2.41, p. 277, expressed by independent least-superset
    laws rather than a selected pair-image construction. *)
Record is_vector_set_sum (V : zmodType) (A B C : set V) : Prop := {
  (** Source for [vector_set_sum_pairs_law]: every original pair sum
      belongs to A+B, Federer 3.2.41, p. 277, defining display. *)
  vector_set_sum_pairs_law : forall a b, A a -> B b -> C (a+b);
  (** Source for [vector_set_sum_least_law]: A+B contains only
      what every set containing all original pair sums contains,
      Federer 3.2.41, p. 277, defining display. *)
  vector_set_sum_least_law : forall D : set V,
    (forall a b, A a -> B b -> D (a+b)) -> C `<=` D
}.

(** Source for [vector_set_sum_laws_membership]: supporting exact
    membership characterization of the independent sum laws for
    Federer 3.2.41, p. 277. No pair witness is globally selected. *)
Theorem vector_set_sum_laws_membership (V : zmodType) (A B C : set V) :
  is_vector_set_sum A B C -> forall z,
  C z <-> exists a b, A a /\ B b /\ z=a+b.
Proof.
move=> hC z; split.
- move=> hz.
  apply: (@vector_set_sum_least_law V A B C hC
    [set x | exists a b, A a /\ B b /\ x=a+b] _ z hz).
  move=> a b ha hb; exists a,b; by split=> //; split.
- move=> [a [b [ha [hb ->]]]].
  exact: (@vector_set_sum_pairs_law V A B C hC a b ha hb).
Qed.

(** Source for [vector_set_sum_unique]: supporting uniqueness
    of the independently specified A+B in Federer 3.2.41, p. 277. *)
Theorem vector_set_sum_unique (V : zmodType) (A B C D : set V) :
  is_vector_set_sum A B C -> is_vector_set_sum A B D -> C=D.
Proof.
move=> hC hD; apply/seteqP; split.
- exact: (@vector_set_sum_least_law V A B C hC D
    (@vector_set_sum_pairs_law V A B D hD)).
- exact: (@vector_set_sum_least_law V A B D hD C
    (@vector_set_sum_pairs_law V A B C hC)).
Qed.
