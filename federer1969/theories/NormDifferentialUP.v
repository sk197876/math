(** Federer (1969), 3.1.1, p. 209: differentiability at an interior point
    is first specified by a continuous linear first-order approximation.
    The finite linear bound and epsilon remainder are intrinsic laws of
    the supplied norms. No finite dimension or completeness is assumed.
    The function is represented by its domain A and a total representative;
    only values on A occur in the defining approximation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_domain_interior]: Federer 3.1.1, p. 209, the condition
    that a belongs to the interior of the domain. In words: some positive
    norm ball of increments about a lies in A. *)
Definition norm_domain_interior (R : realType) (X : lmodType R)
    (NX : X -> R) (A : X -> Prop) (a : X) :=
  exists r : R, 0 < r /\ forall h, NX h < r -> A (a+h).

(** Source for [norm_bounded_linear]: Federer 3.1.1, p. 209, the continuous
    linear approximation L. This finite bound is the equivalent norm-space
    continuity criterion; it does not choose an operator norm. *)
Definition norm_bounded_linear (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (L : Hom X Y) :=
  exists C : R, 0 <= C /\ forall h, NY (L h) <= C * NX h.

(** Source for [has_norm_differential]: Federer 3.1.1, p. 209, first
    definition and displayed limit. In words: at an interior domain point,
    a bounded linear map approximates f with error at most epsilon times
    the increment norm on a sufficiently small ball. The equivalent
    epsilon form includes the zero increment without division by zero. *)
Record has_norm_differential (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) : Prop := {
  (** Source for [norm_differential_interior]: the interior-domain
      requirement in Federer 3.1.1, p. 209, opening definition. *)
  norm_differential_interior : norm_domain_interior NX A a;
  (** Source for [norm_differential_bounded]: the continuous linear
      requirement in Federer 3.1.1, p. 209, opening definition. *)
  norm_differential_bounded : norm_bounded_linear NX NY L;
  (** Source for [norm_differential_remainder]: the vanishing first-order
      remainder of Federer 3.1.1, p. 209, in epsilon form. *)
  norm_differential_remainder : forall e : R, 0 < e ->
    exists d : R, 0 < d /\ forall h, A (a+h) -> NX h < d ->
      NY (f (a+h)-f a-L h) <= e * NX h
}.

(** Source for [norm_differentiable_at]: Federer 3.1.1, p. 209:
    differentiability means existence of the stated linear approximation. *)
Definition norm_differentiable_at (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y) (a : X) :=
  exists L : Hom X Y, has_norm_differential NX NY A f a L.

(** Source for [is_norm_differential_graph]: Federer 3.1.1, p. 209,
    notation Df(a). Specify its exact partial graph before constructing a
    witness: the values are exactly the linear approximations at interior
    domain points. No default differential is assigned elsewhere. *)
Definition is_norm_differential_graph (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (A : X -> Prop) (f : X -> Y)
    (D : partial_function X (Hom X Y)) :=
  forall a L, partial_function_graph D a L <->
    has_norm_differential NX NY A f a L.

(** Source for [norm_domain_interior_member]: supporting consequence of
    a in Int A in Federer 3.1.1, p. 209: f(a) is defined on the domain. *)
Lemma norm_domain_interior_member (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (A : X -> Prop) a :
  norm_domain_interior NX A a -> A a.
Proof.
move=> [r [hr hA]].
have ha := hA 0; rewrite (real_seminorm_zero hNX.1) addr0 in ha.
exact: ha hr.
Qed.
