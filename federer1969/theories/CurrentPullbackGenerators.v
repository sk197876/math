(** Federer (1969), 4.1.7, p. 359:
    the original smooth form pullback acts
    on the coordinate generators described in
    4.1.6, pp. 354–355. Their smoothness
    follows from the previously proved derivative
    class law and the original one-form
    and alternating product identifications. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import AlternatingDual Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormRegularity NormRegularityOperations NormRegularityLinearMaps NormRegularityDerivativeField
  NormRegularityBilinear NormFiniteBilinearBound ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearSealed ContinuousMultilinearOne InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanScalarCoordinateMaps AlternatingForms
  AlternatingProduct AlternatingZero ScalarCoefficients OneFormIdentification OneFormOperatorNorm
  OneFormPullbackIdentification OneFormProducts OneFormProductHead EuclideanCoordinateForms
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentFormInducedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPullbackGenerators.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation PN := (fun m=>@current_form_comass R h2 v m).
Local Notation hPN := (fun m=>@current_form_comass_real_norm R h2 v m).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ej := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hJ 1%N)).
Local Notation operator := (@continuous_multilinear_one_evaluation R X Y (J 1%N)
  NX NY (@ej 1%N) (@JN 1%N) (hJ 1%N)).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.

(** Source for [current_pullback_coordinate_smooth]:
    each actual pulled-back coordinate one-form
    is smooth, supporting the pullback used
    in Federer 4.1.7, p. 359,
    by the original coordinate generators in
    4.1.6, p. 355. F is
    required to be the actual differential
    of the original smooth map. *)
Theorem current_pullback_coordinate_smooth (f:X->Y) (F:X->Hom X Y):
  norm_class_all_orders hNX hNY U f->
  (forall x,U x->has_norm_differential NX NY U f x (F x))->
  forall i:'I_n,norm_class_all_orders hNX (hPN 1%N) U
    (fun x=>A_m_dual (hom_as_linear (F x)) (euclidean_coordinate_form i)).
Proof.
move=>hf hF i.
have [K [hK hBound]]:=@one_form_postoperator_exists R X Y R^o (J 1%N)
  NX NY (fun t:R^o=>`|t|) (PN 1%N) (@current_form_comass_is_induced R h2 v 1%N)
  operator (@JN 1%N) (@continuous_multilinear_one_operator_space R X Y (J 1%N)
    NX NY (@ej 1%N) (@JN 1%N) (hJ 1%N))
  (@euclidean_scalar_coordinate_map R n i) (@euclidean_scalar_coordinate_bounded R n i).
move=>k.
have [G [hClass hActual]]:=@norm_class_derivative_field R X Y NX NY hNX hNY U f k (hf k.+1).
have hPost:=@norm_class_postcompose_linear R X (J 1%N) (A_m X R^o 1)
  NX (@JN 1%N) (PN 1%N) hNX hN1 (hPN 1%N) U G K k hBound hClass.
apply:(norm_class_domain_agreement _ hPost)=>x hx.
have hSame:operator (G x)=F x.
  exact:(norm_differential_unique hNX hNY (hActual x hx) (hF x hx)).
rewrite /euclidean_coordinate_form original_pullback_one_form.
apply:(can_inj (@one_homK R X R^o));apply:hom_ext=>w.
by rewrite hK one_formK hom_compE hSame.
Qed.

(** Source for [current_one_form_product_class]:
    every original finite product of
    class-k one-forms has class k,
    supporting the coordinate-generator pullback in
    Federer 4.1.6, p. 355,
    and 4.1.7, p. 359.
    The empty product and every exterior
    degree use the original algebra. *)
Theorem current_one_form_product_class m (a:'I_m->X->A_m X R^o 1) k:
  (forall i,norm_class hNX (hPN 1%N) U (a i) k)->
  norm_class hNX (hPN m) U
    (fun x=>one_forms_wedge h2 (scalar_bilinear R) 1 (fun i=>a i x)) k.
Proof.
elim:m=>[|m ih] in a *.
- move=>hClass.
  have hConstant:=@norm_class_constant R X (A_m X R^o 0) NX (PN 0%N)
    hNX (hPN 0%N) U (@zero_form R X R^o 1) k hU.
  apply:(norm_class_domain_agreement _ hConstant)=>x hx.
  symmetry;exact:original_one_forms_wedge_empty.
- move=>hClass.
  have [j [b hb]]:=@current_form_finite_basis R h2 v 1%N.
  have [q [c hc]]:=@current_form_finite_basis R h2 v m.
  pose B:=@form_wedge R h2 X R^o (fun a b=>a*b) (@scalar_bilinear R) 1%N m.
  have hB:=@norm_finite_bilinear_bounded R (A_m X R^o 1) (A_m X R^o m)
    (A_m X R^o m.+1) (PN 1%N) (PN m) (PN m.+1) (hPN 1%N) (hPN m) (hPN m.+1)
    j q b c hb hc B (@form_wedge_bilinear R h2 X R^o _ (@scalar_bilinear R) 1%N m).
  have hRest:=ih (fun i:'I_m=>a (lift ord0 i)) (fun i=>hClass (lift ord0 i)).
  have hProduct:=@norm_class_bilinear R X (A_m X R^o 1) (A_m X R^o m)
    (A_m X R^o m.+1) NX (PN 1%N) (PN m) (PN m.+1) hNX (hPN 1%N) (hPN m) (hPN m.+1)
    U (a ord0) (fun x=>one_forms_wedge h2 (scalar_bilinear R) 1
      (fun i:'I_m=>a (lift ord0 i) x)) B k hB (hClass ord0) hRest.
  apply:(norm_class_domain_agreement _ hProduct)=>x hx.
  symmetry;exact:original_one_forms_wedge_head.
Qed.
End CurrentPullbackGenerators.
