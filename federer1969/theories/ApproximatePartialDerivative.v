(** Public approximate partial derivative, Federer (1969), 3.1.2,
    p. 212, accessed only through its opaque exact graph laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations RealNormUP PartialFunctionUP
  ApproximatePartialDerivativeUP ApproximateDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [approximate_partial_derivative]: ap D_i f in
    Federer 3.1.2, p. 212. *)
Definition approximate_partial_derivative (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (i : 'I_n) :=
  @ApproximateDifferential.partial_value R n Y NY hNY A f i.

(** Source for [approximate_partial_derivative_graph]: the exact
    scalar approximate-limit law for ap D_i f(a), Federer 3.1.2, p. 212. *)
Theorem approximate_partial_derivative_graph (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (i : 'I_n) a v :
  partial_function_graph (approximate_partial_derivative hNY A f i) a v <->
    has_approximate_partial_derivative hNY A f a i v.
Proof. exact: ApproximateDifferential.partial_laws. Qed.

(** Source for [approximate_partial_derivative_domain]: the domain of
    ap D_i f in Federer 3.1.2, p. 212, consists exactly of points where
    its defining approximate limit exists. *)
Theorem approximate_partial_derivative_domain (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (i : 'I_n) a :
  partial_function_domain (approximate_partial_derivative hNY A f i) a <->
    exists v, has_approximate_partial_derivative hNY A f a i v.
Proof.
split=> [[v hv]|[v hv]]; exists v.
- exact: (approximate_partial_derivative_graph hNY A f i a v).1 hv.
- exact: (approximate_partial_derivative_graph hNY A f i a v).2 hv.
Qed.
