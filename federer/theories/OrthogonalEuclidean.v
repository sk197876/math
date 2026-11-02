(** Federer (1969), 1.7.2, p. 28: O(n,m) and the orthogonal group O(n). *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates TensorUP.
From Federer Require Import OrthogonalMaps OrthogonalFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module FedererOrthogonal.
Section Euclidean.
Variable R : realFieldType.

(** Source for [O]: Federer 1.7.2, p. 28, O(n,m) is the set of
    orthogonal linear injections from R^m to R^n; target dimension first. *)
Definition O n m : set {linear R_n R m -> R_n R n} :=
  [set f | is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) f].
Arguments O n m : clear implicits.

(** Source for [O_group]: Federer 1.7.2, p. 28, the orthogonal
    group O(n) is O(n,n). The following laws justify the group name. *)
Definition O_group n := O n n.
Arguments O_group n : clear implicits.

(** Source for [O_identity]: Federer 1.7.2, p. 28,
    supporting closure law: identity belongs to the orthogonal group. *)
Lemma O_identity n : O_group n (linear_id (R_n R n)).
Proof. exact: orthogonal_identity. Qed.

(** Source for [O_composition]: Federer 1.7.2, p. 28,
    supporting closure under composition, also for rectangular maps. *)
Lemma O_composition l m n (f : {linear R_n R l -> R_n R m})
    (g : {linear R_n R m -> R_n R n}) :
  O m l f -> O n m g -> O n l (linear_comp g f).
Proof. exact: orthogonal_composition. Qed.

(** Source for [O_inverse]: Federer 1.7.2, p. 28,
    every member of O(n) has a two-sided inverse in O(n). Associativity
    and identity are inherited from composition of linear maps. *)
Theorem O_inverse n (f : {linear R_n R n -> R_n R n}) :
  O_group n f -> exists g : {linear R_n R n -> R_n R n},
    O_group n g /\ cancel f g /\ cancel g f.
Proof.
move=> hf.
have [g [hfg [hgf hg]]] := @orthogonal_endomorphism_inverse_exists R
  (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) f hf.
by exists g; split=> //; split.
Qed.

(** Source for [O_composition_associative]: Federer 1.7.2,
    p. 28, associativity for the composition operation of O(n),
    stated pointwise as for the ambient linear maps. *)
Lemma O_composition_associative n
    (f g h : {linear R_n R n -> R_n R n}) x :
  linear_comp f (linear_comp g h) x = linear_comp (linear_comp f g) h x.
Proof. by []. Qed.

(** Source for [O_identity_left]: Federer 1.7.2, p. 28,
    supporting left identity law inherited from linear-map composition. *)
Lemma O_identity_left n (f : {linear R_n R n -> R_n R n}) x :
  linear_comp (linear_id (R_n R n)) f x = f x.
Proof. by []. Qed.

(** Source for [O_identity_right]: Federer 1.7.2, p. 28,
    supporting right identity law inherited from linear-map composition. *)
Lemma O_identity_right n (f : {linear R_n R n -> R_n R n}) x :
  linear_comp f (linear_id (R_n R n)) x = f x.
Proof. by []. Qed.
End Euclidean.
End FedererOrthogonal.
