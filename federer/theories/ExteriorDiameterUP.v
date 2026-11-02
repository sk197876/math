(** Federer (1969), 2.10.3, pp. 171–172: take the supremum of the norms of
    (a1-b1) wedge ... wedge (am-bm), with all endpoints in the same nonempty
    subset of Euclidean space. Specify this supremum before selecting a
    witness. The target item assumes m positive; m greater than the ambient
    dimension is not excluded. The auxiliary value set includes zero so that
    an empty set also has a nonnegative supporting convention;
    positive-degree nonempty sets already produce zero by taking equal
    endpoints. No relevant local erratum entry occurs. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  FiniteExteriorPowers ExteriorNorm ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_exterior_two_nonzero]: supporting
    characteristic condition for the induced exterior norm
    of Federer 1.7.5, p. 32, used in 2.10.3,
    p. 171. Over the given real field this follows
    from positivity, without a separate scalar-field hypothesis. *)
Lemma real_exterior_two_nonzero (R : realType) : (1+1:R)!=0.
Proof. by change (2%:R!=(0:R)); rewrite pnatr_eq0. Qed.

(** Source for [exterior_difference_product]: direct exterior
    product in the gauge formula of Federer 2.10.3,
    p. 171. The degree and endpoint domain are recorded
    by the common finite ordinal; the product uses only
    the public sealed exterior algebra interface. *)
Definition exterior_difference_product (R : realFieldType) (n m : nat)
    (a b : 'I_m -> R_n R n) : exterior_power (R_n R n) m :=
  @e_lambda R (Choice.clone 'I_m _) (R_n R n) (fun i => a i-b i) m (ord_tuple m).

(** Source for [exterior_difference_norm]: direct Euclidean
    exterior norm in Federer 2.10.3, p. 171, using
    the norm induced in 1.7.5, p. 32. *)
Definition exterior_difference_norm (R : realType) (n m : nat)
    (a b : 'I_m -> R_n R n) : R :=
  @exterior_norm R (real_exterior_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m
    (exterior_difference_product a b).

(** Source for [exterior_difference_norm_nonnegative]:
    supporting nonnegative values for the supremum in
    Federer 2.10.3, p. 171, from the norm laws. *)
Lemma exterior_difference_norm_nonnegative (R : realType) (n m : nat)
    (a b : 'I_m -> R_n R n) : 0<=exterior_difference_norm a b.
Proof. exact: exterior_norm_nonnegative. Qed.

(** Source for [exterior_diameter_values]: direct value
    family for the supremum in Federer 2.10.3,
    p. 171. Adjoin zero for an explicit empty-set
    convention; a later supporting lemma verifies that
    this does not alter the printed positive-degree,
    nonempty-set supremum. *)
Definition exterior_diameter_values (R : realType) (n m : nat) (A : set (R_n R n)) : set R :=
  [set 0] `|` [set d | exists a b : 'I_m -> R_n R n,
    (forall i, A (a i)) /\ (forall i, A (b i)) /\ d=exterior_difference_norm a b].

(** Source for [is_exterior_diameter]: abstract supremum
    specification for Federer 2.10.3, p. 171. This
    does not assume a finite value, boundedness of A
    or existence of maximizing endpoints. *)
Definition is_exterior_diameter (R : realType) (n m : nat)
    (A : set (R_n R n)) (d : \bar R) :=
  is_extended_supremum (exterior_diameter_values m A) d.

(** Source for [exterior_diameter_unique]: supporting
    uniqueness of the supremum used in Federer 2.10.3,
    p. 171, from the abstract least-upper-bound laws. *)
Lemma exterior_diameter_unique (R : realType) (n m : nat)
    (A : set (R_n R n)) (d e : \bar R) :
  is_exterior_diameter m A d -> is_exterior_diameter m A e -> d=e.
Proof. exact: extended_supremum_unique. Qed.

(** Source for [exterior_diameter_nonnegative]: supporting
    nonnegative gauge input in Federer 2.10.3, p. 171.
    This includes the auxiliary empty-set convention. *)
Lemma exterior_diameter_nonnegative (R : realType) (n m : nat)
    (A : set (R_n R n)) (d : \bar R) : is_exterior_diameter m A d -> (0<=d)%E.
Proof.
move=> hd; apply: (extended_supremum_nonnegative hd); exists 0; split=> //; by left.
Qed.
