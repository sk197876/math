(** Federer (1969), 3.2.48, pp. 284, 286: the
    original positive group and isotropy volumes cancel to the
    printed Euler Gamma coefficient. Natural zero dimensions and
    the actual two-atom sphere normalization are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts OrthogonalMaps UnitSphereSpace SphericalOrthogonalProductAlgebra
  SphericalOrthogonalGroupVolume SphericalIsotropyMeasure OrthogonalGroupHausdorffVolume
  OrthogonalGroupHausdorffCarrier StiefelGammaVolumeScalar SphereGammaMass GammaHalfSequences
  EulerGamma EulerGammaHalfParameters SphericalPullbackPushforward SphericalKinematicConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_group_volume_scalar_factorization]: the
    normalization H^nu(O(d+1))=sqrt(2)^d H^mu(I) H^d(Sphere)
    in 3.2.48, p. 284, evaluated with the actual Gamma masses.
    Every positive ambient dimension, including one, is preserved. *)
Lemma spherical_group_volume_scalar_factorization (R:realType) d (c:R_n R (1+d)):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  stiefel_gamma_volume_scalar R (leqnn (1+d))=
    (Num.sqrt (2:R))^+d*stiefel_gamma_volume_scalar R (leqnn d)*
      (2*(euler_gamma_half R)^+(1+d)/gamma_half_sequence R d).
Proof.
move=>hc.
have hMass:=@spherical_orthogonal_group_volume R d c hc.
have hGroup:=@orthogonal_group_hausdorff_total R (1+d)%N.
rewrite /orthogonal_group_hausdorff_measure orthogonal_group_element_full_image in hGroup.
rewrite hGroup (spherical_isotropy_gamma_mass hc) in hMass.
have hSphere:=@hausdorff_unit_sphere_gamma_mass R (1+d)%N (ltn0Sn d).
rewrite subn1 succnK in hSphere.
rewrite hSphere -!EFinM in hMass.
exact (EFin_inj hMass).
Qed.

(** Source for [spherical_kinematic_scalar_cancellation]: all
    positive scalar cancellations in the final display of 3.2.48,
    p. 286. The coarea, fibre similarity, two pullback factors
    and actual group volume give exactly the printed Gamma constant. *)
Theorem spherical_kinematic_scalar_cancellation (R:realType) d k m (c:R_n R (1+d)):
  (d<=k+m)%N ->inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  ((Num.sqrt (2:R))^+((k+m-d)+d*(d-1)%/2)*spherical_preimage_mass_scale R d (k+m-d))^-1*
    (stiefel_gamma_volume_scalar R (leqnn (1+d)))^-1*
    (((Num.sqrt (2:R))^+((d*(d-1)%/2)+(k+m-d)))*
      (gamma_half_sequence R k*gamma_half_sequence R m/
        (gamma_half_sequence R d*gamma_half_sequence R (k+m-d)))*
      (spherical_preimage_mass_scale R d k*spherical_preimage_mass_scale R d m))=
    spherical_kinematic_constant R d k m.
Proof.
move=>hDim hc.
pose s:=Num.sqrt (2:R).
pose g:=stiefel_gamma_volume_scalar R (leqnn d).
pose a:=2*(euler_gamma_half R)^+(1+d)/gamma_half_sequence R d.
pose r:=gamma_half_sequence R k*gamma_half_sequence R m/
  (gamma_half_sequence R d*gamma_half_sequence R (k+m-d)).
pose l:=(k+m-d)%N.
pose mu:=(d*(d-1)%/2)%N.
have hs:s!=0 by rewrite /s gt_eqF // sqrtr_gt0 ltr0n.
have hg:g!=0 by rewrite /g gt_eqF //; exact:stiefel_gamma_volume_scalar_positive.
have ha:a!=0.
  apply:lt0r_neq0; apply:divr_gt0; last exact:gamma_half_sequence_positive.
  apply:mulr_gt0; first by rewrite ltr0n.
  apply:exprn_gt0; exact:euler_gamma_positive.
have hKM:(k+m=d+l)%N by rewrite /l [(d+(k+m-d))%N]addnC subnK.
rewrite (spherical_group_volume_scalar_factorization hc) /spherical_preimage_mass_scale.
change ((s^+(l+mu)*(s^+l*g))^-1*(s^+d*g*a)^-1*
  (s^+(mu+l)*r*((s^+k*g)*(s^+m*g)))=spherical_kinematic_constant R d k m).
have hPowers:s^+(mu+l)*((s^+k*g)*(s^+m*g))=
    (s^+(l+mu)*(s^+l*g))*(s^+d*g).
  have hDegrees:s^+k*s^+m=s^+d*s^+l by rewrite -!exprD hKM.
  have hReorder:s^+(mu+l)*((s^+k*g)*(s^+m*g))=
      s^+(mu+l)*(s^+k*s^+m)*(g*g) by ring.
  rewrite hReorder hDegrees [(mu+l)%N]addnC; ring.
have hReorder:s^+(mu+l)*r*((s^+k*g)*(s^+m*g))=
    (s^+(l+mu)*(s^+l*g))*(s^+d*g)*r.
  rewrite -hPowers; ring.
have hInvC:(s^+(l+mu)*(s^+l*g))^-1=(s^+(l+mu))^-1*((s^+l)^-1*g^-1) by rewrite !invfM.
have hInvV:(s^+d*g*a)^-1=(s^+d)^-1*g^-1*a^-1 by rewrite !invfM.
rewrite hReorder hInvC hInvV.
have hFirst:s^+(l+mu)!=0 by rewrite expf_eq0 (negPf hs) andbF.
have hSecond:s^+l!=0 by rewrite expf_eq0 (negPf hs) andbF.
have hThird:s^+d!=0 by rewrite expf_eq0 (negPf hs) andbF.
have hAlgebra:(s^+(l+mu))^-1*((s^+l)^-1*g^-1)*
    ((s^+d)^-1*g^-1*a^-1)*((s^+(l+mu)*(s^+l*g))*(s^+d*g)*r)=r/a.
  have hRearrange:(s^+(l+mu))^-1*((s^+l)^-1*g^-1)*
      ((s^+d)^-1*g^-1*a^-1)*((s^+(l+mu)*(s^+l*g))*(s^+d*g)*r)=
      ((s^+(l+mu))^-1*s^+(l+mu))*((s^+l)^-1*s^+l)*((s^+d)^-1*s^+d)*
      (g^-1*g)*(g^-1*g)*(r*a^-1) by ring.
  by rewrite hRearrange !mulVf // !mul1r.
rewrite hAlgebra.
exact (@spherical_kinematic_constant_normalization R d k m).
Qed.
