(** Federer (1969), 3.1.1, p. 209: infimum of the differential's
    lengths on unit directions. Specify the greatest homogeneous lower
    bound before proving existence. A finite value requires a nonzero
    source space; the empty unit sphere is treated separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_norm_minimum_modulus]: the infimum over unit vectors
    in Federer 3.1.1, p. 209, specified by its homogeneous lower-bound laws. *)
Record is_norm_minimum_modulus (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (L : Hom X Y) (m : R) : Prop := {
  (** Source for [norm_minimum_nonnegative]: nonnegativity of the
      infimum of image lengths, Federer 3.1.1, p. 209. *)
  norm_minimum_nonnegative : 0 <= m;
  (** Source for [norm_minimum_bound]: homogeneous lower expansion
      bound corresponding to the infimum, Federer 3.1.1, p. 209. *)
  norm_minimum_bound : forall x, m*NX x <= NY (L x);
  (** Source for [norm_minimum_greatest]: greatest lower-bound
      property of the infimum in Federer 3.1.1, p. 209. *)
  norm_minimum_greatest : forall C,
    (forall x, C*NX x <= NY (L x)) -> C <= m
}.

(** Source for [norm_minimum_unique]: supporting uniqueness of the
    infimum specified in Federer 3.1.1, p. 209. *)
Lemma norm_minimum_unique (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (L : Hom X Y) m n :
  is_norm_minimum_modulus NX NY L m ->
  is_norm_minimum_modulus NX NY L n -> m=n.
Proof.
move=> hm hn; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (norm_minimum_greatest hn (norm_minimum_bound hm)).
- exact: (norm_minimum_greatest hm (norm_minimum_bound hn)).
Qed.
