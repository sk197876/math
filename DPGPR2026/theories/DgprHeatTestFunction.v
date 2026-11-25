(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3; blueprint
    dgpr_blueprint.tex, proof of lem:identities(div): the test function
    g(z) = p_s(x-z) y, for 0 < s, x in R^n and y in Y, and its differential
    Dg(z)(v) = - D p_s(x-z)(v) y. The blueprint multiplies g by a function
    phi in D(R^n,R) equal to one on U(0,r_0+1). Here the cutoff replacement
    of Federer 4.1.1, pp. 344-345, supplies a test function equal to g on an
    open set W containing B(0,r); only this property of phi g is used in
    the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm FiniteCoordinates
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain
  NormDifferentialDirectional NormDifferentialLocalAgreement NormBoundedLinearTopology
  NormClassOneUP NormRegularity NormRegularityOperations NormRegularityBilinear
  FiniteNormMetricCompactness SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation SmoothCutoffReplacement.
From DPGPR Require Import DgprHeatKernel DgprHeatKernelDifferential DgprParameterIntegralSmooth
  DgprHeatExtension DgprHeatKernelHigher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section HeatTestFunction.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation hA := (@scalar_absolute_value_norm R).
Variables (Y : lmodType R) (NY : Y -> R).
Hypothesis hNY : is_real_norm NY.

(** Source for [dgpr_identity_bounded]: the identity map of R^n is a
    bounded linear map with constant 1 (Federer 3.1.1, p. 209); supporting
    lem:identities(div). *)
Lemma dgpr_identity_bounded : norm_bounded_linear N N (@dgpr_identity_hom R n).
Proof. by exists 1; split => // h; rewrite mul1r. Qed.

(** Source for [dgpr_reflection_smooth]: the map [z |-> x - z] is of
    class infinity, being the difference of a constant and a bounded
    linear map (Federer 3.1.11, p. 220, and 3.1.1, p. 209); supporting
    lem:identities(div). *)
Lemma dgpr_reflection_smooth (x : X) : norm_class_all_orders hN hN setT (fun z : X => x - z).
Proof.
move=> k.
have hc : norm_class hN hN setT (fun _ : X => x) k.
  by apply: norm_class_constant => a _; exact: dgpr_interior_setT.
have hl := norm_class_linear hN hN k (fun a (_ : setT a) => dgpr_interior_setT a) dgpr_identity_bounded.
exact: (norm_class_subtract hc hl).
Qed.

(** Source for [dgpr_heat_kernel_translate_smooth]: proof of
    lem:identities(div): the function [z |-> p_s(x-z) y] is of class
    infinity for 0 < s, by lem:kernel and Federer 3.1.11, p. 220
    (composition and products). *)
Theorem dgpr_heat_kernel_translate_smooth (s : R) (x : X) (y : Y) : 0 < s ->
  norm_class_all_orders hN hNY setT (fun z => dgpr_heat_kernel s (x - z) *: y).
Proof.
move=> hs k.
apply: norm_class_scalar_product.
- have h := norm_class_composition (dgpr_reflection_smooth x k) (dgpr_kernel_class_infinity n hs k).
  by rewrite dgpr_setT_and in h.
- by apply: norm_class_constant => a _; exact: dgpr_interior_setT.
Qed.

(** Source for [dgpr_reflection_differential]: the differential of
    [w |-> x - w] at every point is the linear map [v |-> -v]
    (Federer 3.1.1, p. 209); supporting lem:identities(div). *)
Lemma dgpr_reflection_differential (x z : X) :
  has_norm_differential N N setT (fun w : X => x - w) z ((-1) *: @dgpr_identity_hom R n).
Proof.
have hI := norm_differential_linear hN hN (dgpr_interior_setT z) dgpr_identity_bounded.
have hS := norm_differential_scale hN hN (-1) hI.
have hC := norm_differential_constant hN hN x (dgpr_interior_setT z).
have h := norm_differential_add hN hC hS.
rewrite add0r in h.
have -> : (fun w : X => x - w) = (fun w => x + (-1) *: (@dgpr_identity_hom R n) w).
  by apply: funext => w; rewrite scaleN1r.
exact: h.
Qed.

(** Source for [dgpr_heat_test_differential]: proof of
    lem:identities(div): the linear map Dg(z) of R^n into Y, for
    g(w) = p_s(x-w) y, given as the composite of [v |-> -v], D p_s(x-z) and
    [t |-> t y]; its values are computed in [dgpr_heat_test_differentialE]. *)
Definition dgpr_heat_test_differential (s : R) (x : X) (y : Y) (z : X) : Hom X Y :=
  hom_comp (dgpr_line_hom y)
    (hom_comp (dgpr_kernel_differential s (x - z)) ((-1) *: @dgpr_identity_hom R n)).

(** Source for [dgpr_hom_oppE]: a linear map commutes with the additive
    inverse; supporting lem:identities(div). *)
Lemma dgpr_hom_oppE (U V : lmodType R) (L : Hom U V) (v : U) : L (- v) = - L v.
Proof. by rewrite -hom_as_linearE linearN hom_as_linearE. Qed.

(** Source for [dgpr_heat_test_differentialE]: proof of
    lem:identities(div), Dg(z)(v) = - D p_s(x-z)(v) y. *)
Lemma dgpr_heat_test_differentialE (s : R) (x : X) (y : Y) (z v : X) :
  dgpr_heat_test_differential s x y z v = - (dgpr_kernel_differential s (x - z) v *: y).
Proof.
rewrite /dgpr_heat_test_differential !hom_compE (hom_scaleE (-1) (@dgpr_identity_hom R n)).
rewrite dgpr_line_homE scaleN1r dgpr_hom_oppE.
exact: scaleNr.
Qed.

(** Source for [dgpr_heat_kernel_translate_differential]: proof of
    lem:identities(div): for 0 < s, the differential of
    [w |-> p_s(x-w) y] at z is Dg(z), by lem:kernel(5) and the chain rule
    of Federer 3.1.1(2), p. 210. *)
Theorem dgpr_heat_kernel_translate_differential (s : R) (x : X) (y : Y) (z : X) : 0 < s ->
  has_norm_differential N NY setT (fun w => dgpr_heat_kernel s (x - w) *: y) z
    (dgpr_heat_test_differential s x y z).
Proof.
move=> hs.
have h1 := norm_differential_chain hN hN hA (dgpr_reflection_differential x z)
  (dgpr_kernel_differential_formula (x - z) hs).
rewrite dgpr_setT_and in h1.
have h2 := norm_differential_chain hN hA hNY h1 (dgpr_line_differential hNY y (p s (x - z))).
by rewrite dgpr_setT_and in h2.
Qed.

Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.

(** Source for [dgpr_heat_kernel_test]: proof of lem:identities(div): for
    0 < s and every r there exist g in D(R^n,Y), its differential field Dg
    and an open set W containing B(0,r) such that g(z) = p_s(x-z) y and
    Dg(z)(v) = - D p_s(x-z)(v) y for z in W. The test function is the
    cutoff replacement of [z |-> p_s(x-z) y] near B(0,r), Federer 4.1.1,
    pp. 344-345; it plays the role of phi g in the blueprint. *)
Theorem dgpr_heat_kernel_test (s r : R) (x : X) (y : Y) : 0 < s ->
  exists (g : smooth_test_space hE) (Dg : X -> Hom X Y) (W : set X),
    @open (real_norm_metric_space hN) W /\ (forall z, N z <= r -> W z) /\
    (forall z, has_norm_differential N NY setT (smooth_test_value hE g) z (Dg z)) /\
    (forall z, W z -> smooth_test_value hE g z = dgpr_heat_kernel s (x - z) *: y /\
       forall v, Dg z v = - (dgpr_kernel_differential s (x - z) v *: y)).
Proof.
move=> hs.
have hU (z : X) (_ : setT z) : norm_domain_interior N setT z := dgpr_interior_setT z.
pose K := @Build_smooth_compact_set R X N hN setT [set z | N z <= r] (@subsetT X _)
  (@finite_norm_metric_ball_compact R X N hN n (@coordinate_basis R n) (@coordinate_basisP R n) r).
have [f hf] := smooth_function_evaluation_surjective hE (dgpr_heat_kernel_translate_smooth x y hs).
pose g := smooth_cutoff_replacement (@coordinate_basisP R n) hU hE K f.
have [W [hW [hKW [_ hWg]]]] :=
  smooth_cutoff_replacement_agrees_near_compact (@coordinate_basisP R n) hU hE K.
have [Dg hDg] := (norm_class_firstP hN hNY setT (smooth_test_value hE g)).1
  (smooth_test_value_smooth hE g 1%N).
have hD (z : X) : has_norm_differential N NY setT (smooth_test_value hE g) z (Dg z).
  exact: (norm_class_one_differential hDg (Logic.I : setT z)).
have hval (z : X) : W z -> smooth_test_value hE g z = dgpr_heat_kernel s (x - z) *: y.
  by move=> hz; rewrite /smooth_test_value hWg // hf.
exists g, Dg, W; split=> //; split; first by move=> z hz; exact: hKW.
split=> // z hz; split; first exact: hval.
have hn : nbhs (z : real_norm_metric_space hN) W by apply: open_nbhs_nbhs; split.
have [d [hd hball]] := (norm_domain_interior_neighbourhood hN W z).2 hn.
have hT := dgpr_heat_kernel_translate_differential x y z hs.
have hT' : has_norm_differential N NY setT (smooth_test_value hE g) z
    (dgpr_heat_test_differential s x y z).
  apply: (norm_differential_local_agreement hN hd _ _ hT) => h hh //.
  by move=> _; rewrite hval //; exact: hball.
by move=> v; rewrite (norm_differential_unique hN hNY (hD z) hT') dgpr_heat_test_differentialE.
Qed.

End HeatTestFunction.
