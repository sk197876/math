(** Public exact approximate differential, Federer (1969), 3.1.2,
    p. 212. All results use the opaque graph specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations RealNormUP PartialFunctionUP
  ApproximateDifferentialUP ApproximateDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [approximate_differential]: ap Df in Federer 3.1.2, p. 212. *)
Definition approximate_differential (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop) (f : R_n R n -> Y) :=
  @ApproximateDifferential.value R n Y NY hNY A f.

(** Source for [approximate_differential_graph]: the exact approximation
    law for ap Df(a), Federer 3.1.2, p. 212. *)
Theorem approximate_differential_graph (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) a L :
  partial_function_graph (approximate_differential hNY A f) a L <->
    has_approximate_differential NY A f a L.
Proof. exact: ApproximateDifferential.laws. Qed.

(** Source for [approximate_differential_domain]: the domain of ap Df
    in Federer 3.1.2, p. 212, is exactly the approximate differentiability
    locus. This does not assert its later measurability properties. *)
Theorem approximate_differential_domain (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) a :
  partial_function_domain (approximate_differential hNY A f) a <->
    approximately_differentiable_at NY A f a.
Proof.
split=> [[L hL]|[L hL]]; exists L.
- exact: (approximate_differential_graph hNY A f a L).1 hL.
- exact: (approximate_differential_graph hNY A f a L).2 hL.
Qed.
