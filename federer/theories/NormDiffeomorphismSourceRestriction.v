(** Federer (1969), 3.1.19, p. 231: shrink a straightening chart
    to an open source neighbourhood, retaining its actual image. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP NormDiffeomorphismUP
  NormDiffeomorphismRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_diffeomorphism_source_restriction]: open source
    restriction of a diffeomorphism, supporting the smaller chart
    neighbourhoods in Federer 3.1.19, p. 231. Its image is the inverse
    image of the smaller source under the actual inverse. *)
Lemma norm_diffeomorphism_source_restriction (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A U:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->X) k :
  is_norm_diffeomorphism hNX hNY A B f g k ->
  (forall x, U x -> A x) -> (forall x, U x -> norm_domain_interior NX U x) ->
  is_norm_diffeomorphism hNX hNY U (fun y=>B y /\ U (g y)) f g k.
Proof.
move=>hD hUA hU.
exact (norm_diffeomorphism_symmetric
  (@norm_diffeomorphism_target_restriction R Y X NY NX hNY hNX B A U g f k
    (norm_diffeomorphism_symmetric hD) hUA hU)).
Qed.
