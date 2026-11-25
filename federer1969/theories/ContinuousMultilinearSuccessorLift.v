(** Federer (1969), 3.1.11, p. 219, as used in 3.1.15, p. 227:
    a bounded linear map L : X -> Z_k into the space of
    continuous k-linear maps is the evaluation of a unique
    element of Z_(k+1) on successor argument families. This
    is the converse of the step elimination rule for
    D^(k+1) f(a) = D(D^k f)(a) and forms the (k+1)-jet of f
    at a from the derivative of D^k f. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  MultilinearArguments MultilinearSuccessorArguments ContinuousMultilinearUncurrying
  MultilinearArgumentTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_successor_lift_exists]:
    the converse of [norm_higher_differential_field_step_elim].
    A bounded linear map L from X into the continuous k-linear
    space is realised by an element z of the continuous
    (k+1)-linear space through adjoining the last argument,
    Federer 3.1.11, p. 219. This supplies the (k+1)st
    differential D(D^k f)(a) from the derivative L of D^k f at a,
    as required for the (k+1)-jet P_a in 3.1.15, p. 227. *)
Theorem continuous_multilinear_successor_lift_exists (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (L : Hom X (Z k)) :
  norm_bounded_linear NX (@ZN k) L ->
  exists z : Z k.+1, forall u v, @ev k u (L v)=@ev k.+1 (multilinear_successor_arguments u v) z.
Proof.
move=> hL.
have [f [hf he]] := continuous_multilinear_uncurry_exists hNX (hZ k) hL.
have hT := continuous_multilinear_argument_transport (addn1 k) (hZ k.+1).
have [z hz] := continuous_multilinear_surjective hT hf.
exists z=> u v.
rewrite -he /multilinear_successor_arguments.
exact: (esym (hz (multilinear_arguments_join u [ffun i : 'I_1=>v]))).
Qed.
