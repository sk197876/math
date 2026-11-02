(** Federer (1969), 3.2.13, p. 250: the radial Gaussian
    integral on positive radii is half Gamma(s). The first
    polar formula in dimension one and its two-point sphere
    compute the half-line integral without an unproved symmetry rule. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate EuclideanInnerProduct
  EuclideanLebesgueDimensions EuclideanFiniteProductIntegral EulerGamma EulerGammaGaussian
  GammaSquareIntegrand PolarSphereFormula RadialSphereIntegral RadialLineSphere
  LebesgueScalarMeasure RealSubsetFiniteScale MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureSubsetIntegral PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gamma_square_integrand_even]: symmetry of the
    whole-line integrand used to evaluate the radial Gaussian
    integral, supporting Federer 3.2.13, p. 250. *)
Lemma gamma_square_integrand_even (R:realType) (s x:R):
  gamma_square_integrand s (-x)=gamma_square_integrand s x.
Proof. by rewrite /gamma_square_integrand normrN !expr2 mulrNN. Qed.

(** Source for [euler_gamma_gaussian_positive_integral]: the
    radial Gaussian integral occurring between the Cartesian and
    angular integrals in Federer 3.2.13, p. 250, equals
    Gamma(s)/2 for each positive s. *)
Theorem euler_gamma_gaussian_positive_integral (R:realType) (s:R) (hs:(0<s)%R):
  is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
    (real_total_integrand (gamma_square_integrand s)) (euler_gamma hs/2)%R%:E.
Proof.
pose g:=fun x:R_n R 1=>gamma_square_integrand s (euclidean_one_project x).
have hI:=euclidean_scalar_function_integral (euler_gamma_gaussian_integral hs).
have [a [hSource hPolar]]:=polar_sphere_integral_formula (ltn0Sn 0%N)
  (ex_intro _ (euler_gamma hs)%:E hI).
have hVal:=measure_integral_unique hSource hI; rewrite hVal in hPolar.
have hTwice:is_measure_subset_integral (@lebesgue_scalar_measure R) [set r:R|(0<r)%R]
    (real_total_integrand (fun r=>(2*gamma_square_integrand s r)%R)) (euler_gamma hs)%:E.
  apply:(measure_integral_graph_equivalent _ hPolar)=>r z.
  case:(pselect ((0<r)%R))=>hr.
  - rewrite (@partial_function_zero_extension_on R (extended_real_line R) 0 [set r:R|(0<r)%R]
      (radial_sphere_integral (real_total_integrand g)) r z hr)
      (@partial_function_zero_extension_on R (extended_real_line R) 0 [set r:R|(0<r)%R]
      (real_total_integrand (fun r=>(2*gamma_square_integrand s r)%R)) r z hr) real_total_integrand_graph.
    have hSphere:=radial_line_sphere_integral g hr.
    have hValue:partial_function_graph (radial_sphere_integral (real_total_integrand g)) r
      (2*gamma_square_integrand s r)%R%:E.
      have hEq:(g (euclidean_one_embed r)+g (euclidean_one_embed (-r)))%R=
          (2*gamma_square_integrand s r)%R.
        rewrite /g !euclidean_one_embedK gamma_square_integrand_even; ring.
      by rewrite -hEq.
    split=>hz.
    + exact:partial_function_single_valued hValue hz.
    + by rewrite -hz.
  - by rewrite (@partial_function_zero_extension_off R (extended_real_line R) 0 [set r:R|(0<r)%R]
      (radial_sphere_integral (real_total_integrand g)) r z hr)
      (@partial_function_zero_extension_off R (extended_real_line R) 0 [set r:R|(0<r)%R]
      (real_total_integrand (fun r=>(2*gamma_square_integrand s r)%R)) r z hr).
have hTwo:(0<(2:R))%R by lra.
have hScaled:=real_subset_integral_cancel_finite_scale (lebesgue_scalar_is_measure R)
  (lt0r_neq0 hTwo) (fun r _=>erefl (2*gamma_square_integrand s r)%R) hTwice.
have hScalar:((2:R)^-1*euler_gamma hs)%R=(euler_gamma hs/2)%R by rewrite mulrC.
by rewrite hScalar in hScaled.
Qed.
