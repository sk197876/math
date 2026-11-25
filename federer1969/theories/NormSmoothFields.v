(** Federer (1969), 3.1.24, pp. 237–239: an
    analytic expansion uses actual differential fields of every order. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity NormClassOneUP NormHigherDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_smooth_fields_exist]: the smooth
    function in conditions (1)–(3) of Federer 3.1.24,
    pp. 237–238, has continuous actual higher differential
    fields in every order, including zero. The existence proof
    selects only already proved class witnesses and does not
    assign values of an actual differential outside its domain. *)
Theorem norm_smooth_fields_exist (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) :
  norm_class_all_orders hNX hNY A f ->
  exists D:forall m,X->@ContinuousMultilinear.space R m X Y NX NY hNX hNY,
    forall m,
      (forall x,A x -> has_norm_higher_differential NX
        (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
        (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY) A f m x (D m x)) /\
      norm_class_zero NX (@ContinuousMultilinear.norm R m X Y NX NY hNX hNY) A (D m).
Proof.
move=>hf.
have hex m:exists D:X->@ContinuousMultilinear.space R m X Y NX NY hNX hNY,
    (forall x,A x -> has_norm_higher_differential NX
      (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
      (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY) A f m x (D x)) /\
    norm_class_zero NX (@ContinuousMultilinear.norm R m X Y NX NY hNX hNY) A D.
  exact (hf m).2.
exists (fun m=>projT1 (cid (hex m)))=>m.
exact (projT2 (cid (hex m))).
Qed.
