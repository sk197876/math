(** Federer (1969), 3.1.21, p. 234: the inverse-continuity
    and closed-range linear-embedding hypotheses, expressed by
    intrinsic laws without selecting an extension of the inverse. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_inverse_continuous_on_set]: continuity of
    (f restricted to S)^-1 at f(a), Federer 3.1.21, p. 234,
    in the epsilon form for its actual image domain. This law
    does not require a total inverse or an open image. *)
Definition norm_inverse_continuous_on_set (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (S:set X) (f:X->Y) a :=
  forall e:R,0<e -> exists d:R,0<d /\
    forall x,S x -> NY (f x-f a)<d -> NX (x-a)<e.

(** Source for [norm_linear_lower_bound]: the continuous inverse
    of the linear homeomorphism onto its range in Federer 3.1.21,
    p. 234, expressed as a positive homogeneous lower bound.
    This does not assume a bounded linear inverse on the whole
    target, which need not exist for a noncomplemented range. *)
Definition norm_linear_lower_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (L:Hom X Y) :=
  exists c:R,0<c /\ forall x,c*NX x<=NY (L x).
