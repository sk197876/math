(** Federer (1969), 4.1.1, p. 345: restriction
    preserves the actual higher differentials on U.
    This supporting locality statement supplies continuity
    and the fixed-support zero-extension comparison. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialLocal
  SmoothFunctionDerivativesUP SmoothRestrictionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section RestrictionDerivatives.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Hypothesis hUV:forall x,U x ->V x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ez := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variables DA:forall k,X->Hom A (Z k).
Variables DB:forall k,X->Hom B (Z k).
Hypothesis hDA:@is_smooth_function_derivatives R X Y NX NY hNX hNY U A evA DA.
Hypothesis hDB:@is_smooth_function_derivatives R X Y NX NY hNX hNY V B evB DB.
Variable L:Hom B A.
Hypothesis hL:is_smooth_restriction U evA evB L.

(** Source for [smooth_restriction_higher_derivative]:
    D^k of the restricted function equals D^k of
    the original function throughout U, supporting
    Federer 4.1.1, p. 345, by the locality
    proved in 3.1.11, p. 219. *)
Theorem smooth_restriction_higher_derivative k f x:U x ->DA k x (L f)=DB k x f.
Proof.
move=>hx.
have hRestr:=@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ez ZN hZ
  k V U (evB f) hUV hU x hx (DB k x f).
have hOrig:=@smooth_derivative_exact R X Y NX NY hNX hNY V B evB DB hDB k f x (@hUV x hx).
have hLocal:=@norm_higher_differential_local_agreement R X Y NX NY hNX hNY Z ez ZN hZ k
  U U U (evA (L f)) (evB f) hU (fun y hy=>iff_refl (U y))
  (fun y hy _=>@hL f y hy) x hx (DB k x f).
exact:(norm_higher_differential_unique hNX hNY hZ
  (@smooth_derivative_exact R X Y NX NY hNX hNY U A evA DA hDA k (L f) x hx)
  (hLocal.2 (hRestr.1 hOrig))).
Qed.
End RestrictionDerivatives.
