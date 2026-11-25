(** Federer (1969), 4.1.7, p. 359:
    the original pullback of a smooth
    differential form is smooth. The proof
    follows the coordinate expansion and pulled-back
    coordinate generators of 4.1.6,
    pp. 352, 354–355, using the
    already proved class calculus throughout. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import AlternatingDual Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  NormRegularityLinearMaps NormRegularityBilinear NormRegularityFiniteSum
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  AlternatingForms ExteriorIndices FiniteExteriorPowers CovectorProducts CovectorProductNaturality
  EuclideanCoordinateForms ExteriorDifferentialCoefficients CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentPullbackGenerators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPullbackClass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation PN := (@current_form_comass R h2 v m).
Local Notation QN := (@current_form_comass R h2 n m).
Local Notation hPN := (@current_form_comass_real_norm R h2 v m).
Local Notation hQN := (@current_form_comass_real_norm R h2 n m).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable f:X->Y.
Variable F:X->Hom X Y.
Hypothesis hF:forall x,U x->has_norm_differential NX NY U f x (F x).
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.

(** Source for [current_pullback_coordinate_product_smooth]:
    the original pullback of DX_lambda
    is a smooth product of actual
    coordinate derivatives, supporting Federer 4.1.7,
    p. 359, by 4.1.6, p. 355.
    The original empty product is retained. *)
Lemma current_pullback_coordinate_product_smooth (lambda:Lambda n m):
  norm_class_all_orders hNX hPN U (fun x=>A_m_dual (hom_as_linear (F x))
    (@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) m lambda)).
Proof.
move=>k.
have hOne i:=@current_pullback_coordinate_smooth R h2 v n U f F hf hF
  (tnth (val lambda) i) k.
have hProduct:=@current_one_form_product_class R h2 v U hU m
  (fun i x=>A_m_dual (hom_as_linear (F x)) (euclidean_coordinate_form (tnth (val lambda) i)))
  k hOne.
apply:(norm_class_domain_agreement _ hProduct)=>x hx.
symmetry;exact:one_forms_wedge_natural.
Qed.

(** Source for [current_smooth_pullback_class]:
    f# phi is an original smooth
    form on U, supporting the pullback
    in Federer 4.1.7, p. 359.
    Only smoothness of f and phi,
    their actual domains and the original
    differential graph are used. *)
Theorem current_smooth_pullback_class (phi:Y->A_m Y R^o m):
  norm_class_all_orders hNY hQN V phi->
  norm_class_all_orders hNX hPN U
    (fun x=>A_m_dual (hom_as_linear (F x)) (phi (f x))).
Proof.
move=>hPhi k.
pose coefficient (lambda:Lambda n m):=@original_form_coefficient_map R Y R^o m
  (e_lambda (@coordinate_basis R n) (val lambda)).
pose omega:=@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) m.
pose term (lambda:Lambda n m) x:=coefficient lambda (phi (f x))*:
  A_m_dual (hom_as_linear (F x)) (omega lambda).
have hTerms lambda:norm_class hNX hPN U (term lambda) k.
  have hBound:=@current_form_linear_bounded R h2 n m R^o (fun t:R^o=>`|t|)
    (@scalar_absolute_value_norm R) (coefficient lambda).
  have hCoeff:=@norm_class_postcompose_linear R Y (A_m Y R^o m) R^o NY QN
    (fun t:R^o=>`|t|) hNY hQN (@scalar_absolute_value_norm R) V phi (coefficient lambda)
    k hBound (hPhi k).
  have hComposite:=@norm_class_compose_on R X Y R^o NX NY (fun t:R^o=>`|t|)
    hNX hNY (@scalar_absolute_value_norm R) U V f (fun y=>coefficient lambda (phi y))
    k hImage (hf k) hCoeff.
  exact:(norm_class_scalar_product hComposite
    (current_pullback_coordinate_product_smooth lambda k)).
have hSum:=@norm_class_finite_sum R X (A_m X R^o m) NX PN hNX hPN U
  (Finite.clone (Lambda n m) _) term k hU hTerms.
apply:(norm_class_domain_agreement _ hSum)=>x hx.
symmetry;rewrite {1}(euclidean_real_form_coordinate_expansion h2 (phi (f x))) linear_sum.
apply:eq_bigr=>lambda _;exact:linearZ.
Qed.
End CurrentPullbackClass.
