(** Federer (1969), 3.1.11, p. 219: the normed
    space of continuous multilinear maps. The May 1987 erratum,
    p. 4, book p. 219 line 4, puts the target norm around
    the value inside the supremum. We specify the equivalent
    least nonnegative homogeneous product bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP TensorFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bounded_multilinear]: continuity of the
    multilinear maps in Federer 3.1.11, p. 219,
    expressed by the homogeneous product bound proved equivalent
    to continuity in the development of 3.1.1(4), p. 210.
    This predicate includes the empty argument family. *)
Definition norm_bounded_multilinear (R : realType) k (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (f : {ffun 'I_k->X}->Y) :=
  multilinear f /\ exists C : R, 0<=C /\
    forall u, NY (f u)<=C*\prod_(i<k) NX (u i).

(** Source for [is_multilinear_operator_norm]: the supremum
    norm in Federer 3.1.11, p. 219, corrected by
    erratum p. 4, book p. 219 line 4. The
    homogeneous bound and its leastness specify the same norm
    without choosing a construction of the multilinear space. *)
Record is_multilinear_operator_norm (R : realType) k (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (f : {ffun 'I_k->X}->Y) (c : R) : Prop := {
  (** Source for [multilinear_operator_nonnegative]: nonnegativity
      of the norm in Federer 3.1.11, p. 219. *)
  multilinear_operator_nonnegative : 0<=c;
  (** Source for [multilinear_operator_bound]: the homogeneous
      evaluation bound from the unit-product supremum in
      Federer 3.1.11, p. 219. *)
  multilinear_operator_bound : forall u, NY (f u)<=c*\prod_(i<k) NX (u i);
  (** Source for [multilinear_operator_least]: leastness of the
      homogeneous bound, equivalent to the supremum specification
      in Federer 3.1.11, p. 219. *)
  multilinear_operator_least : forall C : R, 0<=C ->
    (forall u, NY (f u)<=C*\prod_(i<k) NX (u i)) -> c<=C
}.

(** Source for [is_continuous_multilinear_space]: the space
    of all continuous k-linear maps X^k to Y in Federer
    3.1.11, p. 219. Its elements are specified by
    evaluation, exact representation of bounded multilinear maps,
    and the corrected supremum norm. No symmetry of its elements
    is assumed. *)
Record is_continuous_multilinear_space (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (evaluation : {ffun 'I_k->X}->Hom Z Y) (ZN : Z->R) : Prop := {
  (** Source for [continuous_multilinear_extensional]: equality
      of the multilinear maps in Federer 3.1.11, p. 219,
      is equality at every argument tuple. *)
  continuous_multilinear_extensional : forall z w,
    (forall u, evaluation u z=evaluation u w) -> z=w;
  (** Source for [continuous_multilinear_evaluation]: the
      represented maps are multilinear, as required in Federer
      3.1.11, p. 219. *)
  continuous_multilinear_evaluation : forall z,
    multilinear (fun u=>evaluation u z);
  (** Source for [continuous_multilinear_surjective]: every
      continuous multilinear map belongs to the space of
      Federer 3.1.11, p. 219. *)
  continuous_multilinear_surjective : forall f,
    norm_bounded_multilinear NX NY f -> exists z, forall u, evaluation u z=f u;
  (** Source for [continuous_multilinear_norm_laws]: the norm
      is precisely the corrected norm of Federer 3.1.11,
      p. 219, erratum p. 4, book line 4. *)
  continuous_multilinear_norm_laws : forall z,
    is_multilinear_operator_norm NX NY (fun u=>evaluation u z) (ZN z)
}.
