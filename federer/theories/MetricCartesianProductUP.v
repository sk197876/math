(** Federer (1969), 2.10.27, pp. 190–191: Y, Z and their Cartesian product
    are metrized so that the two projections have Lipschitz constant one.
    Specify the set-theoretic product through pairing and projection laws on
    an abstract metric carrier, with both nonexpanding bounds. No particular
    maximum, sum or Euclidean metric is prescribed, and no isometry of
    slices is assumed from the projection bounds alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_metric_cartesian_product]: abstract
    direct product and projection hypotheses in
    2.10.27, p. 190. Nonexpanding bounds suffice
    for the inequality, including singleton and empty
    factors for which the least constant may be zero. *)
Record is_metric_cartesian_product (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z) : Prop := {
  (** Source for [metric_product_first_pair]: defining
      first-coordinate law of Y times Z in
      2.10.27, p. 190. *)
  metric_product_first_pair : forall y z, first (pair y z)=y;
  (** Source for [metric_product_second_pair]: defining
      second-coordinate law of Y times Z in
      2.10.27, p. 190. *)
  metric_product_second_pair : forall y z, second (pair y z)=z;
  (** Source for [metric_product_pair_coordinates]: defining
      recovery of a product point from its coordinates
      in 2.10.27, p. 190. *)
  metric_product_pair_coordinates : forall p, pair (first p) (second p)=p;
  (** Source for [metric_product_first_nonexpanding]: direct
      first-projection Lipschitz bound in 2.10.27,
      p. 190; exact equality of the least constant
      is unnecessary for the stated inequality. *)
  metric_product_first_nonexpanding : is_metric_lipschitz_bound setT first 1%R;
  (** Source for [metric_product_second_nonexpanding]: direct
      second-projection Lipschitz bound in 2.10.27,
      p. 190. No bound on the pairing is added. *)
  metric_product_second_nonexpanding : is_metric_lipschitz_bound setT second 1%R
}.

(** Source for [metric_product_section]: direct set
    of z with (y,z) in A in the first
    inequality of 2.10.27, p. 190. The
    abstract pairing supplies the product membership. *)
Definition metric_product_section (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (A : set P) (y : Y) : set Z :=
  [set z | A (pair y z)].

(** Source for [metric_product_section_image]: supporting
    identification of the sections in 2.10.27,
    p. 190, with second-coordinate images of
    first-coordinate fibres. Only the product laws,
    not a chosen metric construction, are used. *)
Lemma metric_product_section_image (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z)
    (hp : is_metric_cartesian_product pair first second) (A : set P) y :
  second @` (A `&` first @^-1` [set y])=metric_product_section pair A y.
Proof.
apply/seteqP; split.
- move=> z [p [hpA hpy] <-].
  change (A (pair y (second p))).
  rewrite -(hpy : first p=y) (metric_product_pair_coordinates hp); exact hpA.
- move=> z hz; exists (pair y z); last by rewrite (metric_product_second_pair hp).
  split=> //; change (first (pair y z)=y); by rewrite (metric_product_first_pair hp).
Qed.
