(** Federer (1969), 4.1.7, p. 355: the image
    of E_m(U) in D_m(U) is exactly the compactly
    supported currents. Reuse the proved original
    restriction theorem of 4.1.1, p. 345. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  AlternatingForms CurrentCoefficientNorms CurrentSpaces SmoothDualRestriction
  SmoothDualCompactImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation DD := (@current_space R h2 n U hU m).
Local Notation ED := (@current_smooth_dual_space R h2 n U hU m).
Local Notation rho := (@current_smooth_dual_restriction R h2 n U hU m).

(** Source for [current_smooth_dual_restriction_injective]:
    E_m(U) embeds in D_m(U), Federer 4.1.7,
    p. 355, through the original restriction map. *)
Theorem current_smooth_dual_restriction_injective:injective rho.
Proof.
exact:(@smooth_dual_test_restriction_injective R X Y NX NY hNX hNY U E ev hE D hD
  n (@coordinate_basis R n) (@coordinate_basisP R n) hU).
Qed.

(** Source for [current_compact_support_image]: the image
    consists of exactly all currents with compact
    support in U, Federer 4.1.7, p. 355. *)
Theorem current_compact_support_image (T:DD):
  (exists S:ED,rho S=T) <->
    compact [set x:XT|@current_support R h2 n U hU m T x].
Proof.
exact:(@smooth_dual_restriction_image R X Y NX NY hNX hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE D hD T).
Qed.
End CurrentCompactSupport.
