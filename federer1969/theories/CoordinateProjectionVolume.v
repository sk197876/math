(** Federer (1969), 1.7.4, p. 31, penultimate paragraph: the selected
    covector product factors through p_lambda. Supporting evaluation
    identity for the exterior-power argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerPolarity CoordinateProjection
  AlternatingCoordinates CovectorProducts OneFormProducts ScalarCoefficients
  ExteriorIndices FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_covector]: Federer 1.7.4,
    p. 31, omega_i is the i-th standard coordinate covector,
    obtained by the Euclidean polarity from the standard basis. *)
Definition euclidean_coordinate_covector (R : realFieldType) n (i : 'I_n) :=
  inner_polarity (@euclidean_inner_productP R n) (@coordinate_basis R n i).
Arguments euclidean_coordinate_covector {R n} i.

(** Source for [euclidean_coordinate_covectorE]: Federer
    1.7.4, p. 31, supporting identity omega_i(x)=x_i. *)
Lemma euclidean_coordinate_covectorE (R : realFieldType) n i (x : R_n R n) :
  euclidean_coordinate_covector i [tuple x] = x i.
Proof. by rewrite /euclidean_coordinate_covector inner_polarityE euclidean_inner_basis. Qed.

(** Source for [coordinate_projection_volume_pairing]: Federer
    1.7.4, p. 31, penultimate paragraph: omega_lambda generates
    the image of the top covector map of p_lambda. Here its value
    on an arbitrary product equals the target volume form evaluated
    on the projected product. This includes degree zero. *)
Theorem coordinate_projection_volume_pairing (R : realFieldType)
    (h2 : (1+1 : R) != 0) n m (lambda : Lambda n m)
    (e : 'I_m -> R_n R n) :
  pairing (e_lambda e (ord_tuple m))
    (omega_lambda h2 (@euclidean_coordinate_covector R n) lambda) =
  pairing (e_lambda (fun i => coordinate_projection lambda (e i)) (ord_tuple m))
    (one_forms_wedge h2 (scalar_bilinear R) (1 : R^o)
      (@euclidean_coordinate_covector R m)).
Proof.
rewrite !pairing_e_lambda /omega_lambda
  !(one_forms_wedge_permutations h2 (scalar_bilinear R) (@mulr1 R)).
apply: eq_bigr => sigma _; congr (_ *: _); congr (foldr _ _ _).
apply: eq_map => i.
by rewrite !tnth_map !euclidean_coordinate_covectorE coordinate_projectionE.
Qed.
