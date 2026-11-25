(** Federer (1969), 4.1.6, p. 353: the
    original differentiated coefficient expansion.
    The coefficient differential is an actual linear
    evaluation of D phi, and the fixed coordinate
    products are the earlier Grassmann basis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP Bilinear Alternating AlternatingProduct
  FormEvaluation CoefficientCoordinates OneFormLinear OneFormIdentification ExteriorIndices CovectorProducts
  GrassmannCoordinates GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateTopology
  EuclideanScalarCoordinateMaps EuclideanCoordinateForms
  ScalarCoefficients ScalarTensorContraction MixedAlternatingProduct MixedOrdinaryFormProduct
  ExteriorDifferentialSealed ExteriorDerivativeCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [original_form_coefficient_map]: the
    actual coefficient <e_lambda,phi> in the original
    expansion, Federer 4.1.6, pp. 352–353,
    as a linear map on form values. *)
Definition original_form_coefficient_map (K:fieldType) (V W:lmodType K) m
    (xi:exterior_power V m):Hom (A_m V W m) W:=
  @HomMap K (A_m V W m) W (pairing xi)
    (introT (asboolP _) ((@pairing_bilinear K V W m).2 xi)).

(** Source for [euclidean_linear_one_form_expansion]:
    a linear coefficient differential expands in the
    original DX_j basis, Federer 4.1.6,
    p. 353, without a positive source dimension. *)
Lemma euclidean_linear_one_form_expansion (R:realType) n (L:Hom (R_n R n) R^o):
  one_form L=\sum_(j:'I_n) L (@coordinate_basis R n j)*:euclidean_coordinate_form j.
Proof.
have hLinear:L=\sum_(j:'I_n) L (@coordinate_basis R n j)*:@euclidean_scalar_coordinate_map R n j.
  apply:hom_ext=>v; rewrite hom_sum_coefficientsE.
  change (L v=\sum_(j:'I_n) L (@coordinate_basis R n j)*v j).
  rewrite -{1}(euclidean_coordinate_expansion v) linear_sum.
  apply:eq_bigr=>j _; by rewrite linearZ /= mulrC.
rewrite {1}hLinear linear_sum.
apply:eq_bigr=>j _.
by rewrite linearZ.
Qed.

(** Source for [exterior_differential_coefficient_formula]:
    d phi=sum_lambda d<e_lambda,phi> wedge DX_lambda,
    Federer 4.1.6, p. 353. The ordinary
    coefficient derivatives are the actual composites
    of the coefficient maps with the first differential. *)
Theorem exterior_differential_coefficient_formula (R:realType) (h2:(1+1:R)!=0)
    n m (L:Hom (R_n R n) (A_m (R_n R n) R^o m)):
  form_include (@ExteriorDifferential.value R h2 n R^o m L)=
    \sum_(lambda:Lambda n m) alternating_wedge h2 (scalar_bilinear R)
      (form_include (one_form (hom_comp
        (@original_form_coefficient_map R (R_n R n) R^o m (e_lambda (@coordinate_basis R n) (val lambda))) L)))
      (form_include (@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m lambda)).
Proof.
pose coeff (lambda:Lambda n m):=hom_comp
  (@original_form_coefficient_map R (R_n R n) R^o m (e_lambda (@coordinate_basis R n) (val lambda))) L.
pose omega:=@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m.
pose aw:=@alternating_wedge R h2 (R_n R n) R^o _ (scalar_bilinear R).
pose hb:=@alternating_wedge_bilinear R h2 (R_n R n) R^o _ (scalar_bilinear R).
have hExpand v:form_include (L v)=\sum_(lambda:Lambda n m) coeff lambda v*:form_include (omega lambda).
  rewrite {1}(euclidean_real_form_coordinate_expansion h2 (L v)) linear_sum.
  apply:eq_bigr=>lambda _; by rewrite linearZ.
have hTerm j:
  form_include (mixed_form_product h2 (@scalar_action_bilinear R R^o)
    (euclidean_coordinate_form j) (L (@coordinate_basis R n j)))=
  \sum_(lambda:Lambda n m) coeff lambda (@coordinate_basis R n j)*:
    aw (form_include (euclidean_coordinate_form j)) (form_include (omega lambda)).
  rewrite mixed_real_form_product form_wedge_include hExpand.
  change (aw (form_include (euclidean_coordinate_form j))
    (\sum_(lambda:Lambda n m) coeff lambda (@coordinate_basis R n j)*:form_include (omega lambda))=
    \sum_(lambda:Lambda n m) coeff lambda (@coordinate_basis R n j)*:
      aw (form_include (euclidean_coordinate_form j)) (form_include (omega lambda))).
  rewrite (big_morph (aw (form_include (euclidean_coordinate_form j)))
    (bilDr hb _) (bil0r hb _)).
  apply:eq_bigr=>lambda _; exact:(bilZr hb _ _ _).
rewrite exterior_differential_coordinate_formula linear_sum.
change ((\sum_(j:'I_n) form_include
  (mixed_form_product h2 (@scalar_action_bilinear R R^o)
    (euclidean_coordinate_form j) (L (@coordinate_basis R n j))))=
  \sum_(lambda:Lambda n m) aw (form_include (one_form (coeff lambda))) (form_include (omega lambda))).
under [LHS]eq_bigr do rewrite hTerm.
rewrite exchange_big; apply:eq_bigr=>lambda _.
change ((\sum_(j:'I_n) coeff lambda (@coordinate_basis R n j)*:
  aw (form_include (euclidean_coordinate_form j)) (form_include (omega lambda)))=
  aw (form_include (one_form (coeff lambda))) (form_include (omega lambda))).
rewrite euclidean_linear_one_form_expansion linear_sum.
rewrite (big_morph (fun a=>aw a (form_include (omega lambda)))
  (fun a b=>bilDl hb a b _) (bil0l hb _)).
apply:eq_bigr=>j _.
rewrite linearZ; exact:(esym (bilZl hb _ _ _)).
Qed.
