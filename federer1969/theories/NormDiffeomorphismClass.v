(** Federer (1969), 3.1.18, p. 229: lowering differentiability
    class preserves a diffeomorphism and its actual inverse. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormRegularity NormDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_diffeomorphism_lower]: lowering class for both
    a diffeomorphism and its inverse, supporting the class convention
    of Federer 3.1.18, p. 229, from 3.1.11, p. 220. *)
Lemma norm_diffeomorphism_lower (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->X) k j :
  (j<=k)%N -> is_norm_diffeomorphism hNX hNY A B f g k ->
  is_norm_diffeomorphism hNX hNY A B f g j.
Proof.
move=>hjk [hs hf hg hm hmi hgf hfg]; constructor=>//.
- exact: norm_class_lower hjk hf.
- exact: norm_class_lower hjk hg.
Qed.
