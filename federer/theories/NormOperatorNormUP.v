(** Federer (1969), 3.1.1, pp. 209–210: the operator norm of a
    continuous linear map between arbitrary normed spaces. This extends
    the finite-dimensional inner-product norm of 1.7.6 to the spaces
    used here. The least-bound laws specify the number abstractly. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_norm_operator_norm]: the operator norm in Federer
    3.1.1, pp. 209–210, specified as the least nonnegative constant in
    the homogeneous evaluation bound. No maximum-attainment or finite
    dimensionality is assumed. The closed unit ball includes zero. *)
Record is_norm_operator_norm (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (L : Hom X Y) (n : R) : Prop := {
  (** Source for [norm_operator_nonnegative]: nonnegativity of the
      norm used in Federer 3.1.1, pp. 209–210. *)
  norm_operator_nonnegative : 0 <= n;
  (** Source for [norm_operator_bound]: the evaluation bound for
      the operator norm used in Federer 3.1.1, pp. 209–210. *)
  norm_operator_bound : forall x, NY (L x) <= n*NX x;
  (** Source for [norm_operator_least]: the least-bound property
      of the operator norm in Federer 3.1.1, pp. 209–210. *)
  norm_operator_least : forall C, 0 <= C ->
    (forall x, NY (L x) <= C*NX x) -> n <= C
}.

(** Source for [norm_operator_unique]: supporting uniqueness of
    the operator norm specified in Federer 3.1.1, pp. 209–210. *)
Lemma norm_operator_unique (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (L : Hom X Y) n m :
  is_norm_operator_norm NX NY L n -> is_norm_operator_norm NX NY L m -> n=m.
Proof.
move=> hn hm; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (norm_operator_least hn (norm_operator_nonnegative hm) (norm_operator_bound hm)).
- exact: (norm_operator_least hm (norm_operator_nonnegative hn) (norm_operator_bound hn)).
Qed.
