(** Federer (1969), 3.2.47(3), p. 283: the
    original finite-rectifiability converse and printed mass formula,
    with the exact real coefficient 2^(r/2). Original
    E need not be measurable. The balanced coarea identity
    is proved first; positive scalar cancellation restores this form. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts UnitSphereSpace SphericalProductPreimageImage SphericalOrthogonalProductAlgebra
  SphericalOrthogonalConverseRectifiability SphericalOuterMass RectifiableSetUP HausdorffMeasure
  RealPower RealPowerHalfNatural.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_47_3]: both original conclusions
    of 3.2.47(3), p. 283. Finite Hausdorff
    rectifiability of the WHOLE actual preimage implies finite
    Hausdorff rectifiability of original E, and its mass
    equals 2^(r/2) H^mu(I) H^r(E). No E
    measurability, boundedness, positive degree or extra rank
    hypothesis is added. Ambient dimension one retains both atoms. *)
Theorem federer_3_2_47_3 (R:realType) n (c:R_n R n.+1) (E:set (R_n R n.+1)) r:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E /\
  (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=
    (real_power (2:R) (r%:R/2))%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E)%E.
Proof.
move=>hc hES hRect.
split; first exact (@spherical_orthogonal_converse_rectifiability R n c E r hc hES hRect).
have hBalanced:=@spherical_outer_preimage_mass_balanced R n r c E hc hES hRect.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose rho:=@hausdorff_measure R H (r+n*(n-1)%/2)%N.
pose beta:=@hausdorff_measure R X r.
pose iota:=@hausdorff_measure R H (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c).
pose t:=(Num.sqrt (2:R))^+r.
pose s:=((Num.sqrt (2:R))^-1)^+r.
have hRootPositive:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
have hRootNonzero:Num.sqrt (2:R)!=0 by rewrite gt_eqF.
have hCoefficient:t*s= 1%R.
  by rewrite /t /s -exprMn mulfV // expr1n.
change (s%:E*rho (spherical_orthogonal_preimage c E)=iota*beta E)%E in hBalanced.
have hResult:=congr1 (fun z : \bar R =>(t%:E*z)%E) hBalanced.
rewrite !muleA -EFinM hCoefficient mul1e in hResult.
have hPower:real_power (2:R) (r%:R/2)=t.
  exact (@real_power_half_natural R 2 r ltac:(by rewrite ltr0n)).
rewrite hPower; exact hResult.
Qed.
