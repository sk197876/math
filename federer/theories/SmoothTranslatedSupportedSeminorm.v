(** Federer (1969), 4.1.8, p. 360: the fixed-support
    seminorm estimate used for the original slice operator. A
    translated compactly supported smooth function is bounded, on
    every compact index, by its original same-order support seminorm.
    This reuses the exact translation derivative and off-support laws
    of 4.1.1, pp. 344–346, without an enlargement of that support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  ContinuousMultilinearSealed ContinuousMultilinearNorm SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothDerivativeSupport
  SmoothGlobalTranslationSealed SmoothGlobalTranslationDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothTranslatedSupportedSeminorm.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).

(** Source for [smooth_translated_supported_seminorm_bound]: the
    original support seminorm bounds every translated same-order
    seminorm, supporting the fixed-step continuity of phi_S
    in Federer 4.1.8, p. 360. The translation vector
    and the target compact index are arbitrary. *)
Theorem smooth_translated_supported_seminorm_bound
    (K C:smooth_compact_set hNX (fun _=>True)) i (f:E):
  @smooth_function_support R X Y NX hNX (fun _=>True) E ev f
    `<=` smooth_compact_carrier K->
  forall c,smooth_function_derivative_seminorm hD C i (L c f)<=
    smooth_function_derivative_seminorm hD K i f.
Proof.
move=>hK c.
have hSource:=smooth_function_derivative_seminorm_laws hD K i.
apply:(smooth_derivative_seminorm_least (smooth_function_derivative_seminorm_laws hD C i)).
- exact:(smooth_derivative_seminorm_nonnegative hSource f).
- move=>j hj x hx.
  rewrite (@smooth_global_translation_derivatives R X Y NX NY hNX hNY E ev D hD c
    (L c) (hL c) f j x).
  case:(pselect (smooth_compact_carrier K (x+c)))=>[hInside|hOutside].
  + exact:(smooth_derivative_seminorm_bound hSource f hj hInside).
  + rewrite (@smooth_derivative_outside_compact_support R X Y NX NY hNX hNY
      (fun _=>True) hFull E ev hE D hD K f hK j (x+c) hOutside)
      (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY
        (@ContinuousMultilinear.laws R j X Y NX NY hNX hNY)).1).
    exact:(smooth_derivative_seminorm_nonnegative hSource f).
Qed.
End SmoothTranslatedSupportedSeminorm.
