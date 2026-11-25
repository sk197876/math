(** Federer (1969), 4.1.7, p. 359:
    a bounded Baire form wedged with
    an actual target test belongs to
    the weighted target L1 space.
    The original finite coefficient product bound
    and compact test norm integral prove this
    on arbitrary open domains. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP ScalarCoefficients RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingProduct
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionSubspaceTestValues
  CompactContinuousVectorFields CurrentFormWedgeBound BoundedBilinearCompactLone BaireFunctions
  BoundedBaireFieldLocalIntegral CurrentMeasurableMultiplierUP PartialFunctionBasic MeasureUP
  RadonMeasureUP MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentBaireTestProductLone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation A := (fun m=>A_m X R^o m).
Local Notation AN := (fun m=>@current_form_comass R h2 n m).
Local Notation hAN := (fun m=>@current_form_comass_real_norm R h2 n m).
Local Notation DT := (@current_test_space R h2 n U hU p).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU p).
Local Notation value := (@current_test_value R h2 n U hU p).
Local Notation product := (@form_wedge R h2 X R^o (fun a b=>a*b) (scalar_bilinear R) k p).

(** Source for [current_baire_test_product_lone]:
    the actual original product psi wedge
    phi is L1 for every Radon
    target measure, supporting the Baire
    projection in Federer 4.1.7, p. 359.
    All exterior degrees and empty domains
    are retained. *)
Theorem current_baire_test_product_lone (mu:set UT->\bar R)
    (hm:is_measure mu) (hr:is_radon_measure mu) (psi:UT->A k) (M:R):
  @is_baire_function R UT (real_norm_metric_space (hAN k)) psi->
  0<=M->(forall x,AN k (psi x)<=M)->forall phi:DT,
  is_measure_lp_function mu 1 (partial_function_total
    (fun x:UT=>(product (psi x) (value phi (set_val x)):real_norm_metric_space (hAN (k+p))))).
Proof.
move=>hPsi hM hBound phi.
have hPsiMeas:=(@bounded_baire_field_locally_summable R UT (A k) (AN k) (hAN k)
  mu hm hr psi M hPsi hM hBound).1.
have hProduct:=@current_form_wedge_bounded R h2 n k p.
have hTest:=@smooth_test_original_continuous_field R X (A p) NX (AN p) hNX (hAN p) U
  (@current_smooth_space R h2 n U hU p) (@current_smooth_value R h2 n U hU p) hE phi.
exact:(@bounded_bilinear_compact_lone R UT (A k) (A p) (A (k+p))
  (AN k) (AN p) (AN (k+p)) (hAN k) (hAN p) (hAN (k+p))
  (@current_form_separable R h2 n k) (@current_form_separable R h2 n p)
  (@current_form_separable R h2 n (k+p)) product hProduct mu hm hr psi
  (fun x=>value phi (set_val x)) M hPsiMeas hM hBound hTest).
Qed.
End CurrentBaireTestProductLone.
