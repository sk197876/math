(** Federer (1969), 3.1.11, pp. 218–219:
    intrinsic recursive laws for higher differentials.
    The degree-k values live in an abstract normed space
    of multilinear maps. Differentiation always uses the
    actual domain of the preceding differential. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom PartialFunctionUP NormDifferentialUP
  ContinuousMultilinearUP MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section HigherDifferentialLaws.
Variable R : realType.
Variables X Y : lmodType R.
Variable NX : X->R.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Variable A : X->Prop.
Variable f : X->Y.

(** Source for [has_norm_higher_differential]: the recursion
    D^0 f=f and D^(k+1)f=D(D^k f), with arguments grouped
    as in Federer 3.1.11, pp. 218–219. A total representative
    of D^k f is used only on its exact domain. The higher
    differential is not defined by a default value elsewhere. *)
Fixpoint has_norm_higher_differential (k : nat) : X->Z k->Prop :=
  match k as j return X->Z j->Prop with
  | 0%N => fun a z=>A a /\ @evaluation 0%N [ffun i : 'I_0=>(0:X)] z=f a
  | j.+1 => fun a z=>
      exists g : X->Z j,
        (forall x w, @has_norm_higher_differential j x w -> g x=w) /\
        exists L : Hom X (Z j),
          has_norm_differential NX (@ZN j)
            (fun x=>exists w, @has_norm_higher_differential j x w) g a L /\
          forall u v, @evaluation j u (L v)=
            @evaluation j.+1 (multilinear_successor_arguments u v) z
  end.

(** Source for [is_norm_higher_differential_graph]: the exact
    partial function D^k f in Federer 3.1.11, pp. 218–219.
    A graph must contain precisely the recursive approximations,
    and no values at other points. *)
Definition is_norm_higher_differential_graph k (D : partial_function X (Z k)) :=
  forall a z, partial_function_graph D a z <-> @has_norm_higher_differential k a z.
End HigherDifferentialLaws.

Arguments has_norm_higher_differential {R X Y} NX {Z} evaluation ZN A f k a z.
Arguments is_norm_higher_differential_graph {R X Y} NX {Z} evaluation ZN A f {k} D.
