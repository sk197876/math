(** Federer (1969), 4.1.8, p. 360: the original
    finite covector coordinates control the actual form norm.
    This supporting estimate is the triangle inequality applied
    to the exact expansion of 4.1.6, p. 352. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading ExteriorIndices FiniteExteriorPowers AlternatingForms AlternatingPairing
  CovectorProducts EuclideanCoordinateForms CurrentCoefficientNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFormCoordinateNormBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n d:nat.
Local Notation X := (R_n R n).
Local Notation F := (A_m X R^o d).
Local Notation NF := (@current_form_comass R h2 n d).
Local Notation hNF := (@current_form_comass_real_norm R h2 n d).
Local Notation e := (fun lambda:Lambda n d=>e_lambda (@coordinate_basis R n) (val lambda)).
Local Notation omega := (@omega_lambda R h2 X n (@euclidean_coordinate_form R n) d).

(** Source for [current_form_coordinate_norm_bound]: the actual
    comass is bounded by the weighted sum of its original
    coordinate pairings, supporting the slice-continuity estimate in
    Federer 4.1.8, p. 360. The degree-zero convention
    and the empty coordinate family above dimension are retained. *)
Theorem current_form_coordinate_norm_bound (phi:F):
  NF phi<=\sum_(lambda:Lambda n d) `|pairing (e lambda) phi|*NF (omega lambda).
Proof.
rewrite {1}(@euclidean_real_form_coordinate_expansion R h2 n d phi).
apply:le_trans (@real_seminorm_sum R F NF hNF.1 (Finite.clone (Lambda n d) _)
  (fun lambda=>pairing (e lambda) phi*:omega lambda)) _.
apply:ler_sum=>lambda _;by rewrite (real_seminorm_scale hNF.1).
Qed.
End CurrentFormCoordinateNormBound.
