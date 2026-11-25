(** Federer (1969), 4.1.20, p. 378: the smooth
    pullback of the actual constant target volume by p_lambda
    is the actual original constant DX_lambda. Use the old
    opaque smooth pullback and its actual differential law,
    and the existing coordinate-volume identity; no model of
    the current spaces or exterior algebra is replaced. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct ExteriorIndices AlternatingForms AlternatingDual
  CoordinateProjection CovectorProducts EuclideanCoordinateForms EuclideanCoordinateVolumes
  CurrentSpaces CurrentConstantFields CurrentEuclideanLinearSmooth
  CurrentCoordinateProjectionVolume SmoothFormPullbackUP SmoothFormPullbackSealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CoordinateVolumePullback.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable lambda:Lambda n m.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation Full:=(fun _:Y=>True).
Local Notation hFull:=(fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation p:=(hom_of_linear
  (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _)).
Local Notation hImage:=(fun (x:X) (_:U x)=>Logic.I).
Local Notation hClass:=(@current_euclidean_linear_smooth R n m p U hU).
Local Notation E:=(@current_smooth_space R h2 m Full hFull m).
Local Notation F:=(@current_smooth_space R h2 n U hU m).
Local Notation ev:=(@current_smooth_value R h2 m Full hFull m).
Local Notation fv:=(@current_smooth_value R h2 n U hU m).
Local Notation Pull:=(@SmoothFormPullback.operator R h2 n m m U Full hU hFull
  p hImage hClass).
Local Notation volume:=(@euclidean_volume_covector R m).
Local Notation targetForm:=(@current_constant_form R h2 m Full hFull m volume).
Local Notation coordinateForm:=(@omega_lambda R h2 X n
  (@euclidean_coordinate_form R n) m lambda).

(** Source for [current_coordinate_projection_smooth_volume]:
    p_lambda pullback(DY_1 wedge ... wedge DY_m)=DX_lambda
    on the actual original smooth spaces, the coordinate identity
    used by Federer 4.1.20, p. 378. Every open U and every
    coordinate degree, including zero, is retained. *)
Theorem current_coordinate_projection_smooth_volume:
  Pull targetForm=@current_constant_form R h2 n U hU m coordinateForm.
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n U hU m))=>x hx.
rewrite (@current_constant_form_values R h2 n U hU m coordinateForm x hx).
have hActual:=@current_euclidean_linear_differential R n m p U hU x hx.
have hPull:=@smooth_form_pullback_values R n m m U Full E F ev fv p Pull
  (@SmoothFormPullback.laws R h2 n m m U Full hU hFull p hImage hClass)
  targetForm x p hx hActual.
rewrite hPull (@current_constant_form_values R h2 m Full hFull m volume (p x) Logic.I).
have hVolume:=@current_coordinate_projection_volume_covector R h2 n m lambda.
apply:(eq_trans _ hVolume).
apply:form_ext=>t;rewrite !A_m_dualE.
congr (volume _);apply:eq_from_tnth=>i.
Qed.
End CoordinateVolumePullback.
