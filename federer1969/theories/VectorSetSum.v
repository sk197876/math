(** Public abstract sum for Federer (1969), 3.2.41, printed p. 277.
    All downstream geometry and measure arguments use only the opaque
    independent laws. The private pair-image construction is not imported
    directly or unfolded. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
From Federer Require Import VectorSetSumUP VectorSetSumSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vector_set_sum]: A+B in Federer 3.2.41, p. 277,
    accessed through its existing independent least-set laws. *)
Definition vector_set_sum (V : zmodType) (A B : set V) :=
  @VectorSetSum.value V A B.

(** Source for [vector_set_sum_specification]: independent meaning
    of the opaque A+B, Federer 3.2.41, p. 277. *)
Lemma vector_set_sum_specification (V : zmodType) (A B : set V) :
  is_vector_set_sum A B (vector_set_sum A B).
Proof. exact: VectorSetSum.laws. Qed.

(** Source for [vector_set_sum_membership]: exact original pair
    membership in A+B, Federer 3.2.41, p. 277, defining display. *)
Lemma vector_set_sum_membership (V : zmodType) (A B : set V) z :
  vector_set_sum A B z <-> exists a b, A a /\ B b /\ z=a+b.
Proof. exact (@vector_set_sum_laws_membership V A B (vector_set_sum A B)
  (vector_set_sum_specification A B) z). Qed.

(** Source for [vector_set_sum_contains]: every original x+y
    belongs to A+B, Federer 3.2.41, p. 277, defining display. *)
Lemma vector_set_sum_contains (V : zmodType) (A B : set V) a b :
  A a -> B b -> vector_set_sum A B (a+b).
Proof. exact: (@vector_set_sum_pairs_law V A B (vector_set_sum A B)
  (vector_set_sum_specification A B) a b). Qed.

(** Source for [vector_set_sum_least]: supporting least-set
    form of the definition A+B in Federer 3.2.41, p. 277. *)
Lemma vector_set_sum_least (V : zmodType) (A B D : set V) :
  (forall a b, A a -> B b -> D (a+b)) -> vector_set_sum A B `<=` D.
Proof. exact: (@vector_set_sum_least_law V A B (vector_set_sum A B)
  (vector_set_sum_specification A B) D). Qed.
