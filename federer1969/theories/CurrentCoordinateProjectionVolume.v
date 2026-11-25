(** Federer (1969), 4.1.20, p. 378: the actual
    coordinate projection pulls the target volume covector
    back to DX_lambda. Reuse the proved volume pullback
    of 1.7.4, p. 31, as assembled for 3.2.10, p. 248.
    Identify the original coordinate differentials of 4.1.6,
    p. 351, by their values, without rebuilding exterior algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct ExteriorIndices AlternatingForms AlternatingDual
  OneFormIdentification CoordinateProjection CoordinateProjectionVolume
  EuclideanScalarCoordinateMaps EuclideanCoordinateForms CovectorProducts
  EuclideanCoordinateVolumes EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_coordinate_covector_original_form]:
    the standard coordinate covector in 1.7.4, p. 31,
    is the actual DX_j of 4.1.6, p. 351, used in the
    displayed expansion of Federer 4.1.20, p. 378. *)
Lemma current_coordinate_covector_original_form (R:realType) n (i:'I_n):
  @euclidean_coordinate_covector R n i=@euclidean_coordinate_form R n i.
Proof.
apply:form_ext=>/tupleP[x t];rewrite (tuple0 t).
by rewrite euclidean_coordinate_covectorE /euclidean_coordinate_form
  one_formE /euclidean_scalar_coordinate_map /=.
Qed.

(** Source for [current_coordinate_projection_volume_covector]:
    p_lambda pullback of DY_1 wedge ... wedge DY_m is DX_lambda,
    the second displayed equation of Federer 4.1.20, p. 378.
    The existing induced covector map and original differential
    generators are retained, including degree zero. *)
Theorem current_coordinate_projection_volume_covector (R:realType)
    (h2:(1+1:R)!=0) n m (lambda:Lambda n m):
  A_m_dual (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _)
    (@euclidean_volume_covector R m)=
  @omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m lambda.
Proof.
have hProof:euclidean_two_nonzero R=h2:=Prop_irrelevance _ _.
have hCoordinates:(@euclidean_coordinate_covector R n)=(@euclidean_coordinate_form R n).
  apply:funext=>i;exact:current_coordinate_covector_original_form.
by rewrite coordinate_projection_volume_pullback hProof hCoordinates.
Qed.
