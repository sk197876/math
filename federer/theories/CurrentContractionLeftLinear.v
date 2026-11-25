(** Federer (1969), 4.1.12, p. 368: the
    finite partition argument uses linearity in the
    scalar multiplier. Derive this algebraic law from
    the actual smooth product and test inclusion of
    4.1.7, pp. 355–356. No joint topological
    assertion about the original test topology is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothTestSpaces
  LinearSubspaceRepresentationUP CurrentTestFormProduct SmoothCurrentFormProduct
  SmoothCurrentFormProductBilinear CurrentContraction CurrentEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentContractionLeftLinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation hE d := (@current_smooth_space_laws R h2 n U hU d).
Local Notation DT d := (@current_test_space R h2 n U hU d).
Local Notation inc d := (smooth_test_inclusion (hE d)).
Local Notation C d := (@current_space R h2 n U hU d).
Local Notation action d := (@current_value R h2 n U hU d).
Local Notation product := (@current_test_form_product R h2 n k p U hU).
Local Notation contract := (@current_contraction R h2 n k p U hU).

(** Source for [current_test_form_product_left_linear]:
    multiplication of an actual test by a smooth
    form is linear in that form, supporting the
    original finite partition argument in Federer
    4.1.12, p. 368. *)
Lemma current_test_form_product_left_linear (psi:DT p):linear (fun phi:E k=>product phi psi).
Proof.
move=>c phi chi;apply:(subspace_representation_injective (smooth_test_space_laws (hE (k+p)))).
rewrite (@current_test_form_product_inclusion R h2 n k p U hU (c*:phi+chi) psi)
  (linD (hom_linear (inc (k+p)))) (linZ (hom_linear (inc (k+p))))
  (@current_test_form_product_inclusion R h2 n k p U hU phi psi)
  (@current_test_form_product_inclusion R h2 n k p U hU chi psi).
exact:((@smooth_current_form_product_bilinear R h2 n k p U hU).1 (inc p psi) c phi chi).
Qed.

(** Source for [current_contraction_left_linear]: for
    fixed T, its contraction is linear in the
    original smooth multiplier, supporting the finite
    partition argument in Federer 4.1.12, p. 368.
    The assertion is algebraic and permits arbitrary T. *)
Theorem current_contraction_left_linear (T:C (k+p)):linear (fun phi:E k=>contract phi T).
Proof.
move=>c phi chi;apply:current_values_extensional=>psi.
have hRight:action p (c*:contract phi T+contract chi T) psi=
    c*:action p (contract phi T) psi+action p (contract chi T) psi.
  by rewrite (linearP (action p)) hom_addE hom_scaleE.
rewrite hRight !current_contraction_evaluation.
rewrite (@current_test_form_product_left_linear psi c phi chi).
exact:(hom_linear (action (k+p) T) c (product phi psi) (product chi psi)).
Qed.
End CurrentContractionLeftLinear.
