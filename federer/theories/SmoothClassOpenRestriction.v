(** Federer (1969), 4.1.5, p. 349: the globally
    smooth convolution restricts to the original open
    domain. This uses the proved higher-class restriction
    theorem of 3.1.11, pp. 219–220, in the actual sealed
    multilinear spaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  NormClassHigherRestriction NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [smooth_class_open_restriction]: restriction
    of the smooth convolution to the original open domain,
    supporting Federer 4.1.5, p. 349. The actual higher
    derivatives are retained by the preceding restriction
    theorem. *)
Theorem smooth_class_open_restriction (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U V:X->Prop) (f:X->Y):
  (forall x,V x ->U x) ->
  (forall x,V x ->norm_domain_interior NX V x) ->
  norm_class_all_orders hNX hNY U f ->
  norm_class_all_orders hNX hNY V f.
Proof.
move=>hVU hV hF k.
exact:(@norm_class_higher_open_restriction R X Y NX NY hNX hNY
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY)
  U V f k hVU hV (hF k)).
Qed.
