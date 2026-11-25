(** Federer (1969), 4.1.2, pp. 347-348:
    a scalar smooth remainder multiplied by y has
    every original derivative seminorm bounded by the
    scalar seminorm times the norm of y. This
    makes the kernel-test estimates uniform in y. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP SmoothFunctionTopology
  ScalarVectorSmoothDerivativeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothScalarVectorSeminormBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable S:lmodType R.
Variable scalar_value:S->X->R^o.
Variable DS:forall j,X->Hom S (@ContinuousMultilinear.space R j X R^o NX NS hNX hNS).
Hypothesis hDS:@is_smooth_function_derivatives R X R^o NX NS hNX hNS (fun _=>True) S scalar_value DS.
Variable E:lmodType R.
Variable ev:E->X->Y.
Variable D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.

(** Source for [smooth_scalar_vector_seminorm_bound]: the uniform
    vector-coefficient bound needed for the actual dual norm
    in Federer 4.1.2, p. 347. The scalar
    and vector seminorms use the same compact and order. *)
Theorem smooth_scalar_vector_seminorm_bound (s:S) (f:E) y
    (K:smooth_compact_set hNX (fun _=>True)) i:
  (forall x,ev f x=scalar_value s x*:y) ->
  smooth_function_derivative_seminorm hD K i f<=
    smooth_function_derivative_seminorm hDS K i s*NY y.
Proof.
move=>hValue.
pose p:=smooth_function_derivative_seminorm hDS K i s.
have hP:0<=p:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hDS K i) s.
apply:(smooth_derivative_seminorm_least (smooth_function_derivative_seminorm_laws hD K i)).
- exact:mulr_ge0 hP (real_seminorm_nonnegative hNY.1 y).
- move=>j hj x hx.
  have hG t:=@smooth_derivative_exact R X R^o NX NS hNX hNS (fun _=>True)
    S scalar_value DS hDS j s t Logic.I.
  have h:=@scalar_vector_smooth_derivative_bound R X Y NX NY hNX hNY E ev D hD
    (scalar_value s) j (fun t=>@DS j t s) y f hG hValue x.
  apply:le_trans h _.
  apply:ler_wpM2r; first exact:real_seminorm_nonnegative hNY.1 y.
  exact:(smooth_derivative_seminorm_bound (smooth_function_derivative_seminorm_laws hDS K i)
    s hj hx).
Qed.
End SmoothScalarVectorSeminormBound.
