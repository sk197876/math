(** Federer (1969), 3.2.47, p. 282: the reciprocal of a positive
    residual length is smooth. These representation adapters use the
    actual scalar derivative sequences already proved in 3.1.11 and
    3.1.24, through the sealed multilinear interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity ScalarSquareRootHigherDifferentials ScalarReciprocalHigherDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [scalar_square_root_norm_class]: smooth positive
    square root used in the actual denominators of 3.2.47,
    p. 282, by the proved derivative sequence of 3.1.24, p. 240. *)
Lemma scalar_square_root_norm_class (R:realType) k:
  norm_class (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
    (fun t:R^o=>0<t) Num.sqrt k.
Proof.
pose N:=fun t:R^o=>`|t|.
pose hN:=scalar_absolute_value_norm R.
exact ((@scalar_square_root_higher_differentials R
  (fun j=>@ContinuousMultilinear.space R j R^o R^o N N hN hN)
  (fun j=>@ContinuousMultilinear.evaluation R j R^o R^o N N hN hN)
  (fun j=>@ContinuousMultilinear.norm R j R^o R^o N N hN hN)
  (fun j=>@ContinuousMultilinear.laws R j R^o R^o N N hN hN)).1 k).
Qed.

(** Source for [scalar_reciprocal_norm_class]: smooth reciprocal
    at every nonzero scalar, as used for the positive normalization
    in 3.2.47, p. 282, by 3.1.11, p. 223. *)
Lemma scalar_reciprocal_norm_class (R:realType) k:
  norm_class (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
    (fun t:R^o=>t!=0) (fun t=>t^-1) k.
Proof.
pose N:=fun t:R^o=>`|t|.
pose hN:=scalar_absolute_value_norm R.
exact (@scalar_reciprocal_class_infinity R
  (fun j=>@ContinuousMultilinear.space R j R^o R^o N N hN hN)
  (fun j=>@ContinuousMultilinear.evaluation R j R^o R^o N N hN hN)
  (fun j=>@ContinuousMultilinear.norm R j R^o R^o N N hN hN)
  (fun j=>@ContinuousMultilinear.laws R j R^o R^o N N hN hN) k).
Qed.
