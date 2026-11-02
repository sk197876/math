(** Federer (1969), 3.1.11, p. 220:
    last-pair symmetry in successor-order notation,
    preserving the exact higher-differential graph. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialLastSymmetry
  MultilinearArguments MultilinearSuccessorArguments
  MultilinearArgumentSequence MultilinearDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_last_arguments_symmetric]:
    the last two arguments of D^(n+2) f
    can be exchanged, Federer 3.1.11,
    p. 220. This restates the D^2 D^n
    proof with two successive appended arguments. *)
Theorem norm_higher_differential_last_arguments_symmetric (R : realType) n
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (A : X->Prop) (f : X->Y) a (z : Z n.+2) :
  has_norm_higher_differential NX ez ZN A f n.+2 a z ->
  forall (u : {ffun 'I_n->X}) x y,
    @ez n.+2 (multilinear_successor_arguments (multilinear_successor_arguments u x) y) z=
    @ez n.+2 (multilinear_successor_arguments (multilinear_successor_arguments u y) x) z.
Proof.
move=> hz u x y.
have hdegree : (n+2)%N=n.+2 by rewrite addnS addn1.
pose z' := multilinear_degree_cast Z (esym hdegree) z.
have hz' : has_norm_higher_differential NX ez ZN A f (n+2)%N a z'.
  exact: (@norm_higher_differential_degree_cast R X Y NX Z ez ZN
    A f n.+2 (n+2)%N (esym hdegree) a z).1 hz.
have hs := @norm_higher_differential_last_symmetric R n X Y NX NY
  hNX hNY Z ez ZN hZ A f a z' hz' u x y.
have hl := @multilinear_degree_cast_evaluation R X Y Z ez (n+2)%N n.+2
  hdegree z' (multilinear_arguments_join u
    (multilinear_successor_arguments [ffun i : 'I_1=>x] y)).
have hr := @multilinear_degree_cast_evaluation R X Y Z ez (n+2)%N n.+2
  hdegree z' (multilinear_arguments_join u
    (multilinear_successor_arguments [ffun i : 'I_1=>y] x)).
rewrite multilinear_arguments_join_pair /z' multilinear_degree_cast_inverse_right in hl.
rewrite multilinear_arguments_join_pair /z' multilinear_degree_cast_inverse_right in hr.
by rewrite hl hr.
Qed.
