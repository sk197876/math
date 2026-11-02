(** Federer (1969), 2.6.4, p. 119, final proposition: the product of
    arbitrary Daniell integrals on K(X), K(Y). We specify its Daniell laws
    and the value on every separated product, which is the displayed tensor
    diagram on generators. Existence and uniqueness on K(X times Y) must be
    proved. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_daniell_product]: abstract specification of
    the final product functional and commutative diagram in Federer
    2.6.4, p. 119. The functionals need not be monotone. *)
Definition is_daniell_product (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) (C : ((X*Y) -> R) -> R) :=
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) C /\
  forall f g, compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
    C (fun p : X*Y => f p.1*g p.2)=A f*B g.
