(** Federer (1969), 3.4.7, p. 324: the
    actual first nonzero derivative has null bad
    directions for both ambient Lebesgue measure and
    unit-sphere Hausdorff measure. The polynomial is
    proved to be the actual derivative diagonal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness PolynomialFunctions ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP
  AnalyticGermJetsSealed AnalyticGermDiagonalNonzero AnalyticGermDirectionalPolynomial
  EuclideanLebesgueDimensions EuclideanPolynomialSphereNull HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_analytic_germ_exceptional_directions_null]:
    both displayed nullity assertions of 3.4.7,
    p. 324, for the original derivative at
    the original centre. The stronger supporting formulation
    needs only nonzero D^k; the first-order and
    lower-jet conditions are used for the almost-everywhere
    regular-direction consequence. *)
Theorem euclidean_analytic_germ_exceptional_directions_null (R:realType) n
    (a:R_n R n) k
    (alpha:analytic_germ_space (inner_norm_real_norm (@euclidean_inner_productP R n)) a):
  let NX:=inner_norm (@euclidean_inner_productP R n) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R n) in
  let diagonal:=fun v:R_n R n=>@ContinuousMultilinear.evaluation R k (R_n R n) R^o
    NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
      (@AnalyticGermJets.value R (R_n R n) NX hNX a k alpha) in
  @AnalyticGermJets.value R (R_n R n) NX hNX a k alpha<>0 ->
  @euclidean_lebesgue_measure R n [set v|diagonal v = 0] = 0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
    [set v|diagonal v = 0 /\NX v = 1] = 0%:E.
Proof.
move=>NX hNX diagonal hJet.
have [P [hHomogeneous hValues]]:=@analytic_germ_directional_polynomial_exists
  R (R_n R n) NX hNX a k alpha.
have [v hv]:=@analytic_germ_nonzero_jet_diagonal R (R_n R n) NX hNX a k alpha hJet.
have hNonzero:exists x,P x<>0.
  exists v;by rewrite hValues.
have hFunction:(P:R_n R n->R) = diagonal.
  apply:funext=>x;exact:hValues x.
have hAmbient:=@euclidean_polynomial_zero_set_null R n P hNonzero.
have hSphere:=@euclidean_homogeneous_polynomial_unit_sphere_null R n k P hHomogeneous hNonzero.
rewrite hFunction in hAmbient hSphere.
by split.
Qed.
