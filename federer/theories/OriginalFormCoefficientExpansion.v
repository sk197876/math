(** Federer (1969), 4.1.6, p. 352: the original
    coordinate expansion retains arbitrary vector
    coefficients. Reuse the proved 1.4.4 coefficient
    expansion and identify its dual basis with the
    original increasing products of coordinate covectors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom ExteriorGrading ExteriorIndices LinearBasis FiniteDualDimension FiniteExteriorPowers
  AlternatingForms AlternatingIsomorphism AlternatingPairing GrassmannCoordinates
  CoefficientCoordinates CovectorProducts GrassmannAbbreviations FiniteCoordinates
  PointwiseFieldSpaceUP PointwiseFieldSpaceSealed DifferentialFormFields EuclideanCoordinateForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OriginalFormCoefficientExpansion.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variables V W:lmodType K.
Variables n m:nat.
Variable e:'I_n->V.
Hypothesis he:is_basis e.
Variable omega:'I_n->A_m V K^o 1.
Hypothesis hDual:forall i j,omega i [tuple e j]=if i==j then 1 else 0.
Local Notation el := (fun lambda:Lambda n m=>e_lambda e (val lambda)).
Local Notation heb := (finite_e_lambda_basis he h2 m).
Local Notation wl := (@omega_lambda K h2 V n omega m).

(** Source for [original_product_dual_basis]: the original
    coordinate products are the actual dual exterior
    basis, Federer 4.1.6, pp. 351–352. *)
Lemma original_product_dual_basis (lambda:Lambda n m):
  hom_to_form (dual_basis heb lambda)=wl lambda.
Proof.
apply:pairing_ext=>xi.
apply:(@basis_linear_ext K (Choice.clone (Lambda n m) _)
  (exterior_power V m) el heb K^o
  (hom_as_linear (form_to_hom (hom_to_form (dual_basis heb lambda))))
  (hom_as_linear (form_to_hom (wl lambda)))) xi=>mu.
change (pairing (el mu) (hom_to_form (dual_basis heb lambda))=pairing (el mu) (wl lambda)).
by rewrite {1}/pairing hom_to_formK dual_basisE (pairing_e_omega h2 hDual) eq_sym.
Qed.

(** Source for [original_form_coefficient_expansion]: the
    original sum over increasing coordinate products,
    Federer 4.1.6, p. 352, with arbitrary vector
    coefficients W as stated in the following paragraph.
    All exterior degrees remain in the assertion. *)
Theorem original_form_coefficient_expansion (phi:A_m V W m):
  phi=\sum_(lambda:Lambda n m) form_with_coefficient (pairing (el lambda) phi) (wl lambda).
Proof.
rewrite {1}(@form_coefficient_expansion K V W m (Finite.clone (Lambda n m) _) el heb phi).
apply:eq_bigr=>lambda _; by rewrite original_product_dual_basis.
Qed.
End OriginalFormCoefficientExpansion.

(** Source for [differential_form_original_coordinate_expansion]:
    the original field expansion of Federer 4.1.6,
    p. 352, at every original point of the domain,
    with arbitrary coefficients and no regularity premise. *)
Theorem differential_form_original_coordinate_expansion (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) (W:lmodType R) n m (phi:differential_form_space R X (R_n R n) W m):
  forall x,@differential_form_value R X (R_n R n) W m phi x=
    \sum_(lambda:Lambda n m) form_with_coefficient
      (pairing (e_lambda (@coordinate_basis R n) (val lambda))
        (@differential_form_value R X (R_n R n) W m phi x))
      (@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m lambda).
Proof.
move=>x; exact:(@original_form_coefficient_expansion R h2 (R_n R n) W n m
  (@coordinate_basis R n) (@coordinate_basisP R n) (@euclidean_coordinate_form R n)
  (@euclidean_coordinate_form_dual R n) (@differential_form_value R X (R_n R n) W m phi x)).
Qed.
