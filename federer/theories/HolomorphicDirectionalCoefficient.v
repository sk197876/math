(** Federer (1969), 3.4.12, p. 339: the original divided
    derivative coefficient fields are holomorphic. Apply actual fixed
    derivative evaluation and real factorial scaling of the same target. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  AnalyticDirectionalCoefficient HolomorphicUP HolomorphicDerivativeEvaluation HolomorphicScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coefficients.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variables (hNX:is_complex_norm NX) (hNY:is_complex_norm NY).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNYR:=(complex_norm_real hNY).

(** Source for [holomorphic_directional_coefficient_exists]: actual
    holomorphic divided coefficient fields in each original direction,
    extending 3.4.6, pp. 322–323, under 3.4.12, p. 339. *)
Theorem holomorphic_directional_coefficient_exists (A:set X) (f:X->Y) k (v:X):
  is_holomorphic hNXR hNYR A f ->exists c:X->Y,
    @is_analytic_directional_coefficient R XR YR NX NY hNXR hNYR A f k v c /\
    is_holomorphic hNXR hNYR A c.
Proof.
move=>hF.
have [g [hG hHolomorphic]]:=@holomorphic_derivative_evaluation_exists R X Y NX NY hNX hNY
  A f k [ffun _:'I_k=>v] hF.
exists (fun x=>ComplexScalars.embed R (((k`!)%:R:R)^-1)*:g x);split.
- move=>x hx z hz;by rewrite (hG x hx z hz).
- exact:(@holomorphic_scale R X Y NX NY hNXR hNY A g
    (ComplexScalars.embed R (((k`!)%:R:R)^-1)) hHolomorphic).
Qed.
End Coefficients.
