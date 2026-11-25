(** Federer (1969), 4.1.9, p. 364: the original
    affine homotopy mass integrand is bounded by
    |g-f| times the printed convex power of endpoint
    differential norms. The original operator norm,
    every exterior degree and both zero endpoints remain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional NormDifferentialLocal NormDifferentialLinear
  NormDifferentialChain NormDifferentialArithmetic NormFiniteLinearBound NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCurveJacobian
  CurrentMapDifferential CurrentCartesianAffineSlice CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopySliceClass CurrentHomotopyTimeVelocity
  CurrentAffineHomotopyDifferential CurrentExteriorOperatorMassBound EuclideanOperatorConvexBound
  EuclideanHomOperator OperatorNormUP OperatorNormSealed ExteriorGrading ExteriorPowers
  ExteriorMaps ExteriorHomogeneousProducts CurrentCoefficientNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentAffineHomotopyMassIntegrand.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation W := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation slice := (@current_homotopy_slice_map R n nu h).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hHomotopy).
Local Notation P := (@euclidean_first_injection_map R 1%N n).
Local Notation Point t x := (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).
Hypothesis hAffine:forall t x,A t->U x->slice t x=(1-t)*:f x+t*:g x.
Arguments hAffine : clear implicits.


Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation Df x := (@current_map_differential R n nu U f x).
Local Notation Dg x := (@current_map_differential R n nu U g x).
Local Notation Ds t x := (@current_map_differential R n nu U (slice t) x).
Local Notation Velocity t x := (@current_homotopy_time_velocity R n nu A U h t x).
Local Notation VectorMass := (@current_vector_mass R h2 n j).
Local Notation ImageMass t x eta := (@current_vector_mass R h2 nu (1+j)
  (exterior_product (exterior_first_inclusion Y (Velocity t x))
    (exterior_power_map (hom_as_linear (Ds t x)) j eta))).
Local Notation Law F := (@OperatorNorm.laws R X Y (@euclidean_inner_product R n)
  (@euclidean_inner_product R nu) (@euclidean_inner_productP R n) (@euclidean_inner_productP R nu)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (hom_as_linear F)).

(** Source for [current_affine_homotopy_mass_integrand_bound]:
    the original norm of h-dot_t wedge Lambda_j Dh_t eta
    is bounded by |g-f|[(1-t)||Df||+t||Dg||]^j for
    every unit-ball eta, supporting the first affine
    mass estimate in Federer 4.1.9, p. 364.
    No simplicity of eta or positivity of j is used. *)
Theorem current_affine_homotopy_mass_integrand_bound t x (eta:exterior_power X j):
  0<=t<=1->U x->VectorMass eta<=1->
  ImageMass t x eta<=NY (g x-f x)*((1-t)*Op (Df x)+t*Op (Dg x))^+j.
Proof.
move=>ht hx hEta.
have hAt:=@current_homotopy_closed_time_band R A hInterval t ht.
have hVelocity:=@current_affine_homotopy_time_velocity R n nu A U V f g h hHomotopy hAffine t x hAt hx.
have hSpace:=@current_affine_homotopy_space_differential R n nu A U V f g h hHomotopy hAffine t x hAt hx.
have hMass:=@current_homotopy_mass_integrand_bound R h2 n nu j (hom_as_linear (Ds t x))
  (Op (Ds t x)) (Law (Ds t x)) (Velocity t x) eta.
apply:(le_trans hMass).
have hPositive:0<=NY (Velocity t x)*(Op (Ds t x))^+j.
  exact:mulr_ge0 (inner_norm_nonnegative (@euclidean_inner_productP R nu) _)
    (exprn_ge0 j (operator_norm_nonnegative (Law (Ds t x)))).
apply:(le_trans (ler_wpM2l hPositive hEta)).
rewrite mulr1 hVelocity hSpace.
exact:(ler_wpM2l (inner_norm_nonnegative (@euclidean_inner_productP R nu) (g x-f x))
  (@euclidean_operator_convex_power_bound R n nu (Df x) (Dg x) t j ht)).
Qed.
End CurrentAffineHomotopyMassIntegrand.
