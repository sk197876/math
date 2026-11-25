(** Federer (1969), 3.1.11, p. 220:
    every existing higher differential is symmetric.
    The proof follows the printed induction using
    D^2 D^(k-2), together with the identities
    inherited from the preceding differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals fingroup perm.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialArgumentIdentity
  NormHigherDifferentialLastArguments FiniteArgumentPermutation
  MultilinearSuccessorPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_symmetric]:
    Federer 3.1.11, p. 220, the
    statement that D^k f(a) is a
    symmetric k-form whenever f is k
    times differentiable at a. Symmetry is
    proved from the exact graph, never assumed
    in the multilinear-space definition. *)
Theorem norm_higher_differential_symmetric (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (A : X->Prop) (f : X->Y) k :
  forall a (z : Z k),
    has_norm_higher_differential NX ez ZN A f k a z ->
    forall (s : 'S_k) u, @ez k (finite_argument_permutation s u) z=@ez k u z.
Proof.
elim: k=>[|k ih] a z hz s u.
- have he : finite_argument_permutation s u=u.
    apply/ffunP=>i; by have := ltn_ord i; rewrite ltn0.
  by rewrite he.
- case: k ih a z hz s u=>[|n] ih a z hz s u.
  + have he : finite_argument_permutation s u=u.
      apply/ffunP=>i; rewrite /finite_argument_permutation ffunE.
      by rewrite (ord1 i) (ord1 (s ord0)).
    by rewrite he.
  + apply: (multilinear_prefix_last_pair_symmetric
      (F:=fun w=>@ez n.+2 w z))=>[s' v x|v x y].
    * apply: (@norm_higher_differential_inherit_argument_identity R n.+1
        X Y NX NY hNX hNY Z ez ZN hZ A f a z
        (finite_argument_permutation s' v) v _ hz x).
      move=> b w hw; exact: ih b w hw s' v.
    * exact: (@norm_higher_differential_last_arguments_symmetric R n
        X Y NX NY hNX hNY Z ez ZN hZ A f a z hz v x y).
Qed.
