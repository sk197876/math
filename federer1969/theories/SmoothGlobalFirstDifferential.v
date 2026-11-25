(** Federer (1969), 4.1.1, p. 346: the
    actual first differential of a global smooth
    test is a continuous differential field.
    This reuses the class-one equivalence and
    uniqueness already proved in 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional NormClassOneUP
  NormRegularity ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormHigherDifferentialFirst SmoothFunctionSpaceUP SmoothFunctionDerivativesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section GlobalFirstDifferential.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ez := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.

(** Source for [smooth_global_first_differential]: the
    actual first multilinear differential regarded
    as an ordinary continuous linear map,
    supporting Federer 4.1.1, p. 346. *)
Definition smooth_global_first_differential f x:Hom X Y:=
  @continuous_multilinear_one_operator R X Y (Z 1%N) NX NY (@ez 1%N) (@ZN 1%N)
    (hZ 1%N) (@D 1%N x f).

(** Source for [smooth_global_first_differential_class_one]:
    the exact first differential is a continuous
    differential field for the original smooth
    function, supporting Federer 4.1.1, p. 346. *)
Theorem smooth_global_first_differential_class_one f:
  is_norm_class_one_field NX NY (fun _=>True) (ev f) (smooth_global_first_differential f).
Proof.
have hClass:=smooth_function_evaluation_smooth hE f 1%N.
have [M hM]:=(@norm_class_firstP R X Y NX NY hNX hNY (fun _=>True) (ev f)).1 hClass.
have hSame:M=smooth_global_first_differential f.
  apply:funext=>x.
  have hActual:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z ez ZN hZ
    (fun _=>True) (ev f) x (@D 1%N x f)).1
    (@smooth_derivative_exact R X Y NX NY hNX hNY (fun _=>True) E ev D hD 1%N f x Logic.I).
  exact:(norm_differential_unique hNX hNY (norm_class_one_differential hM Logic.I) hActual).
by rewrite -hSame.
Qed.
End GlobalFirstDifferential.
