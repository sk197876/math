(** Federer (1969), 4.1.6, p. 353: the
    coefficient derivatives in the original expansion
    are actual norm differentials. Evaluation on a
    standard exterior word has norm at most one,
    so no coefficient-space dimension is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  Alternating AlternatingProduct ExteriorIndices CovectorProducts GrassmannAbbreviations FiniteCoordinates
  EuclideanCoordinateForms EuclideanInnerProduct EuclideanCoordinateMetric InnerNorm HilbertFormCompactness
  ScalarCoefficients AlternatingFormNormUP AlternatingFormUnitBounds
  ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDerivativeUP ExteriorDifferentialCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [original_form_coefficient_bound]: the
    original coefficient <e_lambda,phi> is bounded
    by the induced form norm,
    supporting Federer 4.1.6, p. 353. *)
Lemma original_form_coefficient_bound (R:realType) n (W:lmodType R) m
    (NW:W->R) (P:A_m (R_n R n) W m->R)
    (hP:is_alternating_form_norm (inner_norm (@euclidean_inner_productP R n)) NW P)
    (lambda:Lambda n m) (phi:A_m (R_n R n) W m):
  NW (@original_form_coefficient_map R (R_n R n) W m
    (e_lambda (@coordinate_basis R n) (val lambda)) phi)<=P phi.
Proof.
change (NW (pairing (e_lambda (@coordinate_basis R n) (val lambda)) phi)<=P phi).
rewrite pairing_e_lambda.
apply:(alternating_form_unit_tuple_bound (inner_norm_real_norm (@euclidean_inner_productP R n)) (hP phi)).
move=>i; rewrite tnth_map euclidean_coordinate_unit_norm; exact:lexx.
Qed.

(** Source for [original_form_coefficient_differential]:
    D<e_lambda,phi>=<e_lambda,D phi>,
    the actual coefficient differentiation used in
    Federer 4.1.6, p. 353. *)
Theorem original_form_coefficient_differential (R:realType) n (W:lmodType R) m
    (NW:W->R) (P:A_m (R_n R n) W m->R)
    (hP:is_alternating_form_norm (inner_norm (@euclidean_inner_productP R n)) NW P)
    (U:R_n R n->Prop) (phi:R_n R n->A_m (R_n R n) W m) a
    (L:Hom (R_n R n) (A_m (R_n R n) W m)):
  has_norm_differential (inner_norm (@euclidean_inner_productP R n)) P U phi a L->
  forall lambda:Lambda n m,
    let C:=@original_form_coefficient_map R (R_n R n) W m
      (e_lambda (@coordinate_basis R n) (val lambda)) in
    has_norm_differential (inner_norm (@euclidean_inner_productP R n)) NW U
      (fun x=>C (phi x)) a (hom_comp C L).
Proof.
move=>hL lambda C.
have hBound:norm_bounded_linear P NW C.
  exists 1; split; first exact:ler01.
  move=>b; rewrite mul1r; exact:original_form_coefficient_bound.
exact:(norm_differential_postcompose (inner_norm_real_norm (@euclidean_inner_productP R n)) hL hBound).
Qed.

(** Source for [real_exterior_derivative_original_coefficients]:
    the original coefficient expansion of d phi,
    Federer 4.1.6, p. 353, with each
    displayed coefficient differential certified on
    the actual original function domain. *)
Theorem real_exterior_derivative_original_coefficients (R:realType) (h2:(1+1:R)!=0) n m
    (P:A_m (R_n R n) R^o m->R)
    (hP:is_alternating_form_norm (inner_norm (@euclidean_inner_productP R n)) (fun c:R^o=>`|c|) P)
    (U:R_n R n->Prop) (phi:R_n R n->A_m (R_n R n) R^o m) a b:
  has_exterior_derivative (inner_norm (@euclidean_inner_productP R n)) P U phi a b->
  exists L:Hom (R_n R n) (A_m (R_n R n) R^o m),
    has_norm_differential (inner_norm (@euclidean_inner_productP R n)) P U phi a L /\
    (forall lambda:Lambda n m,
      let C:=@original_form_coefficient_map R (R_n R n) R^o m
        (e_lambda (@coordinate_basis R n) (val lambda)) in
      has_norm_differential (inner_norm (@euclidean_inner_productP R n)) (fun c:R^o=>`|c|) U
        (fun x=>C (phi x)) a (hom_comp C L)) /\
    form_include b=\sum_(lambda:Lambda n m) alternating_wedge h2 (scalar_bilinear R)
      (form_include (OneFormIdentification.one_form (hom_comp
        (@original_form_coefficient_map R (R_n R n) R^o m
          (e_lambda (@coordinate_basis R n) (val lambda))) L)))
      (form_include (@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m lambda)).
Proof.
move=>[L [hL hB]]; exists L; split=>//; split.
- exact:(original_form_coefficient_differential hP hL).
- have hEqual:=exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n R^o m L) hB.
  rewrite -hEqual; exact:exterior_differential_coefficient_formula.
Qed.
