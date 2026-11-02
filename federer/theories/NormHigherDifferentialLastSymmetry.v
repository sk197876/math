(** Federer (1969), 3.1.11, p. 220:
    symmetry of the final two arguments of a
    higher differential, obtained from the second
    differential of D^(k-2) f. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferential
  NormHigherDifferentialIterated NormSecondDifferential
  MultilinearArguments MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_last_symmetric]:
    the D^2 D^(k-2) step in the
    symmetry proof of Federer 3.1.11,
    p. 220, using the proved bilinear
    symmetry on p. 219. The exact
    domain of the lower differential is retained. *)
Theorem norm_higher_differential_last_symmetric (R : realType) n
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (A : X->Prop) (f : X->Y) a (z : Z (n+2)%N) :
  has_norm_higher_differential NX ez ZN A f (n+2)%N a z ->
  forall (u : {ffun 'I_n->X}) x y,
    @ez (n+2)%N (multilinear_arguments_join u
      (multilinear_successor_arguments [ffun i : 'I_1=>x] y)) z=
    @ez (n+2)%N (multilinear_arguments_join u
      (multilinear_successor_arguments [ffun i : 'I_1=>y] x)) z.
Proof.
move=> hz u x y.
have [G hG] := @norm_higher_differential_representative_exists
  R X Y NX NY hNX hNY Z ez ZN hZ A f n.
pose NP := @ZN n.
have hNP := continuous_multilinear_norm_is_norm hNY (@hZ n).
pose W q := @ContinuousMultilinear.space R q X (Z n) NX NP hNX hNP.
pose ew q := @ContinuousMultilinear.evaluation R q X (Z n) NX NP hNX hNP.
pose WN q := @ContinuousMultilinear.norm R q X (Z n) NX NP hNX hNP.
have hW q := @ContinuousMultilinear.laws R q X (Z n) NX NP hNX hNP.
have [w [hw he]] := (@norm_higher_differential_iterated R n 2%N X Y NX NY
  hNX hNY Z ez ZN hZ W ew WN hW A f G a z hG).1 hz.
pose B a := exists v, has_norm_higher_differential NX ez ZN A f n a v.
have hs := @norm_second_differential_symmetric R X (Z n) NX NP
  hNX hNP W ew WN hW B G a w hw x y.
by rewrite -!he hs.
Qed.
