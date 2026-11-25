(** Federer (1969), 4.1.7, p. 357: on a
    connected open set avoiding the boundary
    support, a top current is a real
    multiple of E^n. The proof applies
    the already proved 4.1.4 theorem to
    the actual finite covector target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers ExteriorDeterminant
  AlternatingForms AlternatingPairing CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  CurrentVectorSpaces CurrentMultivectorDual FiniteMultivectorDual MultivectorDualSealed
  CurrentDirectionalDerivative CurrentBoundary CurrentSupportGeometry CurrentSupportAgreement
  CurrentOpenConstantDensity TopCurrentDerivativeSupport SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  DistributionConstancy MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [top_current_constancy_from_derivative_support]:
    the original application of 4.1.4 to
    Y=A^n(R^n), supporting Federer 4.1.7,
    p. 357. The top exterior power
    is a line, so the representing
    functional is a real coordinate multiple.
    Empty A and dimension zero are retained. *)
Theorem top_current_constancy_from_derivative_support (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU n) (A:set (R_n R n)):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) A ->
  @connected (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) A ->
  A `<=` U ->
  (forall j,@current_support R h2 n U hU n
    (@current_directional_derivative R h2 n n U hU (@coordinate_basis R n j) T) `<=` (U `&` ~` A)) ->
  exists c:R,@current_support R h2 n U hU n
    (T-c*:@euclidean_fundamental_current_open R h2 n U hU) `<=` (U `&` ~` A).
Proof.
move=>hOpen hConnected hAU hDerivatives.
pose X:=R_n R n.
pose Y:=A_m X R^o n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose NY:=@current_form_comass R h2 n n.
pose hNY:=@current_form_comass_real_norm R h2 n n.
pose E:=@current_smooth_space R h2 n U hU n.
pose ev:=@current_smooth_value R h2 n U hU n.
pose hE:=@current_smooth_space_laws R h2 n U hU n.
pose D:=@current_smooth_derivatives R h2 n U hU n.
pose hD:=@current_smooth_derivative_laws R h2 n U hU n.
have[alpha [hAlpha hRepresentation]]:=@distribution_derivative_support_constant R n Y NY hNY
  (@current_form_complete R h2 n n) E ev U hU hE D hD T A hOpen hConnected hAU hDerivatives.
have[d [b hb]]:=@current_vector_finite_basis R h2 n n.
have[a hA]:=@finite_multivector_dual_surjective R X n [the finType of 'I_d] b hb alpha.
pose c:=@top_coordinate R h2 n X (@coordinate_basis R n) (@coordinate_basisP R n) a.
have hTop:a=c*:e_lambda (@coordinate_basis R n) (ord_tuple n).
  exact:(@top_expansion R h2 n X (@coordinate_basis R n) (@coordinate_basisP R n) a).
pose S:=@current_open_constant_density R h2 n n U hU a.
have hS:S=c*:@euclidean_fundamental_current_open R h2 n U hU.
  rewrite /S hTop linearZ;by [].
exists c;rewrite -hS.
apply:(@current_support_difference_agreement R h2 n n U hU T S A hOpen)=>psi hPsi.
have hT:=hRepresentation psi hPsi.
have hDensity:=@current_open_constant_density_action R h2 n n U hU a psi.
have hEq:(fun x=>alpha (@current_test_value R h2 n U hU n psi x))=
    (fun x=>pairing a (@current_test_value R h2 n U hU n psi x)).
  apply:funext=>x;rewrite -hA;exact:MultivectorDual.laws.
rewrite hEq in hT.
exact:(congr1 (@fine R) (measure_integral_unique hT hDensity)).
Qed.

(** Source for [top_current_constancy]: the original
    positive-dimensional constancy theorem, Federer
    4.1.7, p. 357: the difference
    from c E^n restricted to U has
    support outside connected open A when
    the boundary support avoids A. *)
Theorem top_current_constancy (R:realType) (h2:(1+1:R)!=0) p
    (U:set (R_n R p.+1))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R p.+1)) U x)
    (T:@current_space R h2 p.+1 U hU p.+1) (A:set (R_n R p.+1)):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p.+1))) A ->
  @connected (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p.+1))) A ->
  A `<=` U ->
  @current_support R h2 p.+1 U hU p (@current_boundary R h2 p.+1 p U hU T) `<=` (U `&` ~` A) ->
  exists c:R,@current_support R h2 p.+1 U hU p.+1
    (T-c*:@euclidean_fundamental_current_open R h2 p.+1 U hU) `<=` (U `&` ~` A).
Proof.
move=>hOpen hConnected hAU hBoundary.
apply:(@top_current_constancy_from_derivative_support R h2 p.+1 U hU T A hOpen hConnected hAU).
exact:(@top_current_coordinate_derivative_support R h2 p U hU T A hOpen hBoundary).
Qed.

(** Source for [zero_dimensional_top_current_constancy]:
    the dimension-zero endpoint of the original
    constancy argument in Federer 4.1.7,
    p. 357, from 4.1.4 without
    introducing a negative-degree boundary. *)
Theorem zero_dimensional_top_current_constancy (R:realType) (h2:(1+1:R)!=0)
    (U:set (R_n R 0))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R 0)) U x)
    (T:@current_space R h2 0 U hU 0) (A:set (R_n R 0)):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 0))) A ->
  @connected (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 0))) A ->
  A `<=` U ->exists c:R,@current_support R h2 0 U hU 0
    (T-c*:@euclidean_fundamental_current_open R h2 0 U hU) `<=` (U `&` ~` A).
Proof.
move=>hOpen hConnected hAU.
apply:(@top_current_constancy_from_derivative_support R h2 0 U hU T A hOpen hConnected hAU).
move=>j;have h:=ltn_ord j;by rewrite ltn0 in h.
Qed.
