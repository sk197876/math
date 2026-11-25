(** Federer (1969), 3.2.13, p. 250: Gamma(s) is the
    integral of exp(-y^2)|y|^(2s-1) on the whole real line.
    Bounded square substitutions and increasing convergence establish
    integrability; the printed value at the origin is retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal lra ring.
From Federer Require Import EulerGamma EulerGammaMeasurable EulerGammaDerivativeIntegral
  GammaSquareIntegrand GammaSquareSourceGraph GammaSquareTargetMultiplicity GammaSquareCutoffLaws
  GammaSquareBoundedIntegral RealNonnegativeIntegralValueLimit RealIncreasingIntegralLimit
  LebesgueScalarMeasure MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureIntegralAlmostEquality MeasureAlmostUP MeasureAlmostBasic PartialFunctionUP PartialFunctionBasic
  SummableRealFunctionUP SummableRealArithmetic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [euler_gamma_gaussian_zero_integral]: the square
    substitution identity with the auxiliary origin value zero,
    supporting Federer 3.2.13, p. 250. Its proof establishes
    the finite Gaussian integral without assuming it. *)
Lemma euler_gamma_gaussian_zero_integral (R:realType) (s:R) (hs:0<s):
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (gamma_square_zero_completion s)) (euler_gamma hs)%:E.
Proof.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
pose f n:=gamma_square_target_cutoff s ((2:R)^+n).
pose g n:=gamma_square_source_cutoff s ((2:R)^+n).
have hI n:exists a,is_measure_integral mu (real_total_integrand (f n)) a.
  exact:gamma_square_target_integral_exists hs.
pose a n:=proj1_sig (cid (hI n)).
have hT n:is_measure_integral mu (real_total_integrand (f n)) (a n).
  exact:(proj2_sig (cid (hI n))).
have hTwo:0<(2:R) by lra.
have hS n:is_measure_integral mu (real_total_integrand (g n)) (a n).
  exact:gamma_square_bounded_integral_transfer (exprn_gt0 n hTwo) (hT n).
have hFull:=@real_total_integral_scale R R mu hm (gamma_positive_completion s)
  (euler_gamma hs) 2 (euler_gamma_completed_integral hs).
have hLimit:=@real_nonnegative_integral_value_limit R R mu hm f
  (fun x=>2*gamma_positive_completion s x) a (2*euler_gamma hs)%:E
  (fun n x=>(gamma_square_cutoffs_nonnegative s ((2:R)^+n) x).2)
  (fun n x=>(gamma_square_cutoffs_monotone s x n).2)
  (fun x=>(gamma_square_cutoffs_pointwise_limit s x).2) hT hFull.
have hSource:=@real_nonnegative_increasing_integral_limit R R mu hm g
  (fun x=>2*gamma_square_zero_completion s x) a (2*euler_gamma hs)%:E
  (fun n x=>(gamma_square_cutoffs_nonnegative s ((2:R)^+n) x).1)
  (fun n x=>(gamma_square_cutoffs_monotone s x n).1)
  (fun x=>(gamma_square_cutoffs_pointwise_limit s x).1) hS hLimit.
have hHalf:=@real_total_integral_scale R R mu hm
  (fun x=>2*gamma_square_zero_completion s x) (2*euler_gamma hs) (1/2) hSource.
have hFun:(fun x=>1/2*(2*gamma_square_zero_completion s x))=gamma_square_zero_completion s.
  by apply:funext=>x; field; lra.
have hValue:1/2*(2*euler_gamma hs)=euler_gamma hs by field; lra.
by rewrite hFun hValue in hHalf.
Qed.

(** Source for [euler_gamma_gaussian_integral]: the displayed
    whole-line Gamma identity in Federer 3.2.13, p. 250,
    for every s>0. Null modification restores the printed value
    at zero, including 0^0= 1 when s= 1/2. *)
Theorem euler_gamma_gaussian_integral (R:realType) (s:R) (hs:0<s):
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (gamma_square_integrand s)) (euler_gamma hs)%:E.
Proof.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
apply:(measure_integral_almost_equal hm (euler_gamma_gaussian_zero_integral hs)).
apply:(@measure_null_subset R R mu hm _ [set 0]); last exact:lebesgue_scalar_singleton.
move=>x hx; apply:contrapT=>hNot.
apply:hx; exists (gamma_square_integrand s x)%:E; split; apply/real_total_integrand_graph=>//.
have hNe:x!= 0 by apply/eqP=>he; apply:hNot; exact:he.
by rewrite /gamma_square_zero_completion (negbTE hNe).
Qed.
