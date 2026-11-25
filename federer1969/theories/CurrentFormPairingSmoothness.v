(** Federer (1969), 4.1.8, p. 360: smoothness of every
    scalar multivector pairing proves smoothness of the original
    finite-dimensional covector field. The proof reuses the exact
    coordinate expansion of 4.1.6, p. 352, rather than constructing
    a new dual space or imposing a regularity hypothesis on it. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  NormRegularityOperations NormRegularityBilinear NormRegularityFiniteSum
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  ExteriorIndices AlternatingForms AlternatingIsomorphism AlternatingPairing
  CoefficientCoordinates CovectorProducts EuclideanCoordinateForms
  OriginalFormCoefficientExpansion CurrentCoefficientNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentFormPairingSmoothness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variables n d:nat.
Local Notation Y := (R_n R n).
Local Notation F := (A_m Y R^o d).
Local Notation NF := (@current_form_comass R h2 n d).
Local Notation hNF := (@current_form_comass_real_norm R h2 n d).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.

(** Source for [current_form_scalar_coefficient]: scalar
    coefficients in the original expansion of Federer 4.1.6,
    p. 352, are the original scalar multiples. This supporting
    identity uses only the earlier exterior-form identification. *)
Lemma current_form_scalar_coefficient (c:R^o) (omega:F):
  form_with_coefficient c omega=c*:omega.
Proof.
apply:form_ext=>t.
rewrite /form_with_coefficient hom_to_formE hom_with_coefficientE form_scaleE.
change ((form_to_hom omega (e_lambda idfun t):R)*c=c*(omega t)).
by rewrite -pairing_tuple /pairing mulrC.
Qed.

(** Source for [current_form_field_smooth_from_pairings]: the
    covector phi_S in Federer 4.1.8, p. 360, is smooth
    once its printed scalar pairings are smooth. The finite
    coordinate proof covers degrees above the ambient dimension
    and the zero-dimensional source without extra assumptions. *)
Theorem current_form_field_smooth_from_pairings (f:X->F):
  (forall eta:exterior_power Y d,norm_class_all_orders hNX hNS U
    (fun x=>pairing eta (f x)))->
  norm_class_all_orders hNX hNF U f.
Proof.
move=>hPair k.
pose omega:=@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) d.
pose e:=fun lambda:Lambda n d=>e_lambda (@coordinate_basis R n) (val lambda).
pose g:=fun (lambda:Lambda n d) (x:X)=>pairing (e lambda) (f x)*:omega lambda.
have hSum:norm_class hNX hNF U (fun x=>\sum_(lambda:Lambda n d) g lambda x) k.
  apply:(@norm_class_finite_sum R X F NX NF hNX hNF U (Finite.clone (Lambda n d) _)
    g k hU)=>lambda.
  apply:(@norm_class_scalar_product R X F NX NF hNX hNF U
    (fun x=>pairing (e lambda) (f x)) (fun _=>omega lambda) k).
  - exact:(hPair (e lambda) k).
  - exact:(@norm_class_constant R X F NX NF hNX hNF U (omega lambda) k hU).
apply:(@norm_class_domain_agreement R X F NX NF hNX hNF U
  (fun x=>\sum_(lambda:Lambda n d) g lambda x) f k _ hSum)=>x _.
have hExpansion:=@original_form_coefficient_expansion R h2 Y R^o n d
  (@coordinate_basis R n) (@coordinate_basisP R n) (@euclidean_coordinate_form R n)
  (@euclidean_coordinate_form_dual R n) (f x).
symmetry;rewrite {1}hExpansion;apply:eq_bigr=>lambda _.
exact:current_form_scalar_coefficient.
Qed.
End CurrentFormPairingSmoothness.
