(** Public differential Df of Federer (1969), 3.1.1, p. 209.
    Downstream results use the exact graph law; the witness is opaque. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP
  NormDifferentialUP NormDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_differential]: notation Df in Federer 3.1.1,
    p. 209, interpreted as the partial function with exactly the
    differentiability domain. No value is supplied elsewhere. *)
Definition norm_differential (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y) :=
  @NormDifferential.value R X Y NX NY hNX hNY A f.

(** Source for [norm_differential_graph]: exact defining law for Df(a)
    in Federer 3.1.1, p. 209. *)
Theorem norm_differential_graph (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y) a L :
  partial_function_graph (norm_differential hNX hNY A f) a L <->
    has_norm_differential NX NY A f a L.
Proof. exact: NormDifferential.laws. Qed.

(** Source for [norm_differential_domain]: the domain of Df discussed
    in Federer 3.1.1, pp. 209–211, is precisely the differentiability
    locus; this is its exact specification, not a measurability theorem. *)
Theorem norm_differential_domain (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y) a :
  partial_function_domain (norm_differential hNX hNY A f) a <->
    norm_differentiable_at NX NY A f a.
Proof.
split=> [[L hL]|[L hL]]; exists L.
- exact: (proj1 (norm_differential_graph hNX hNY A f a L) hL).
- exact: (proj2 (norm_differential_graph hNX hNY A f a L) hL).
Qed.
