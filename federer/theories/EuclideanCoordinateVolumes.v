(** Federer (1969), 3.2.10, p. 248: supporting unit-coordinate
    volumes in the Jacobian calculation, using 1.5.2, p. 22,
    and 1.7.5, pp. 32–33. All exterior operations use the
    existing opaque interfaces; dimension zero is included. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom HomogeneousHom TensorUP GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps CoordinateProjection BasisInterpolation
  CoordinateProjectionVolume ExteriorGrading ExteriorMaps ExteriorMapScaling
  ExteriorDeterminant FiniteExteriorPowers ExteriorFrameUnitNorm
  AlternatingCoordinates AlternatingDual AlternatingPairing CovectorProducts
  OneFormProducts ScalarCoefficients InnerExteriorBasis ExteriorCovectorInner
  InnerExteriorPositivity ExteriorNorm InitialIndices DualityBasis
  CovectorProductNaturality ExteriorOperatorEstimate SimpleAdaptedBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_volume_covector]: the unit target
    volume used to compute the exterior norm in Federer 3.2.10,
    p. 248, expanded by 1.7.5, p. 33. *)
Definition euclidean_volume_covector (R:realType) n :=
  omega_lambda (euclidean_two_nonzero R)
    (@euclidean_coordinate_covector R n) (Lambda_top n).

(** Source for [euclidean_volume_covector_unit]: Federer 3.2.10,
    p. 248, supporting unit normalization inherited from
    1.7.5, pp. 32–33, including the empty top product. *)
Lemma euclidean_volume_covector_unit (R:realType) n:
  exterior_covector_norm (euclidean_two_nonzero R)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n)
    (euclidean_volume_covector R n)= 1.
Proof.
rewrite /euclidean_volume_covector /euclidean_coordinate_covector
  -inner_exterior_basis_covectors inner_exterior_form_norm.
exact:euclidean_top_product_unit_norm.
Qed.

(** Source for [coordinate_projection_volume_pullback]: the
    coordinate projection in Federer 3.2.10, p. 248, pulls the
    target unit volume back to the selected coordinate form.
    Supporting form of 1.7.4, p. 31. *)
Lemma coordinate_projection_volume_pullback (R:realType) m n
    (lambda:Lambda m n):
  A_m_dual (GRing.Linear.clone _ _ _ _ (@coordinate_projection R m n lambda) _)
    (euclidean_volume_covector R n)=
  omega_lambda (euclidean_two_nonzero R) (@euclidean_coordinate_covector R m) lambda.
Proof.
rewrite /euclidean_volume_covector omega_lambda_top_product one_forms_wedge_natural
  /omega_lambda.
congr (one_forms_wedge _ _ _ _); apply:funext=>i.
apply:form_ext=>/tupleP[x t]; rewrite (tuple0 t).
rewrite A_m_dualE.
change ((@euclidean_coordinate_covector R n i) [tuple coordinate_projection lambda x]=
  (@euclidean_coordinate_covector R m (tnth (val lambda) i)) [tuple x]).
by rewrite !euclidean_coordinate_covectorE coordinate_projectionE.
Qed.

(** Source for [coordinate_injection_top_product]: Federer
    3.2.10, p. 248, supporting description of the complementary
    coordinate volume; this is the induced-map law of 1.3.1,
    pp. 12–13, on the coordinate injection from 1.7.4, p. 31. *)
Lemma coordinate_injection_top_product (R:realType) m k (lambda:Lambda m k):
  exterior_power_map (@coordinate_injection R m k lambda) k
    (e_lambda (@coordinate_basis R k) (ord_tuple k))=
  e_lambda (@coordinate_basis R m) (val lambda).
Proof.
rewrite exterior_map_indexed_product (indexed_productE (@coordinate_basis R m) (val lambda)).
have he:(fun i:'I_k=>@coordinate_injection R m k lambda (@coordinate_basis R k i))=
    (fun i=>@coordinate_basis R m (tnth (val lambda) i)).
  apply:funext=>i; by rewrite /coordinate_injection basis_interpolationE.
by rewrite he.
Qed.
