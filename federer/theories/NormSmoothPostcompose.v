(** Federer (1969), 4.1.7, pp. 355–356: fixed
    linear coefficient operations on smooth forms are
    smooth. This supporting law reuses the bounded
    linear case of 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  ContinuousMultilinearSealed NormRegularity NormClassHigherPostcompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_smooth_postcompose]: bounded linear
    changes of coefficient space preserve the original
    class-infinity fields, supporting the current
    operations of Federer 4.1.7, pp. 355–356. *)
Theorem norm_smooth_postcompose (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (U:X->Prop) (f:X->Y) (L:Hom Y Z):
  norm_bounded_linear NY NZ L ->
  norm_class_all_orders hNX hNY U f ->
  norm_class_all_orders hNX hNZ U (fun x=>L (f x)).
Proof.
move=>hL hf k.
exact:(@norm_class_higher_postcompose R X Y Z NX NY NZ hNX hNY hNZ
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j X Z NX NZ hNX hNZ)
  (fun j=>@ContinuousMultilinear.norm R j X Z NX NZ hNX hNZ)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j X Z NX NZ hNX hNZ)
  U f L k hL (hf k)).
Qed.
