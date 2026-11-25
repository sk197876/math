(** Federer (1969), 4.1.7, p. 357: outside
    the support of a top current's boundary,
    every coordinate derivative vanishes. This
    is the original reduction to 4.1.4
    through (boundary T) wedge e_j=(-1)^n D_j T. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct CurrentSpaces CurrentDirectionalDerivative
  CurrentBoundary CurrentPointEvaluation CurrentSupportGeometry CurrentSupportAgreement TopCurrentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [top_current_coordinate_derivative_support]:
    spt(boundary T) contained in U minus A
    implies the same for every D_j T,
    supporting the original constancy theorem in
    Federer 4.1.7, p. 357. *)
Theorem top_current_coordinate_derivative_support (R:realType) (h2:(1+1:R)!=0) p
    (U:set (R_n R p.+1))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R p.+1)) U x)
    (T:@current_space R h2 p.+1 U hU p.+1) (A:set (R_n R p.+1)):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p.+1))) A ->
  (@current_support R h2 p.+1 U hU p (@current_boundary R h2 p.+1 p U hU T)
    `<=` (U `&` ~` A)) ->forall j,
  @current_support R h2 p.+1 U hU p.+1
    (@current_directional_derivative R h2 p.+1 p.+1 U hU (@coordinate_basis R p.+1 j) T)
    `<=` (U `&` ~` A).
Proof.
move=>hA hBoundary j.
pose D:=@current_directional_derivative R h2 p.+1 p.+1 U hU (@coordinate_basis R p.+1 j) T.
have hZero (psi:@current_test_space R h2 p.+1 U hU p.+1):
    @current_test_support R h2 p.+1 p.+1 U hU psi `<=` A ->
    @current_value R h2 p.+1 U hU p.+1 D psi=0.
  move=>hPsi.
  have hAction:@current_value R h2 p.+1 U hU p.+1
      (@top_current_vector_product R h2 p U hU j (@current_boundary R h2 p.+1 p U hU T)) psi=0.
    rewrite top_current_vector_product_evaluation.
    apply:current_test_disjoint_support_zero=>x hx hSupp.
    apply:(hBoundary x hx).2;apply:hPsi.
    exact:(@top_current_vector_test_support R h2 p U hU j psi x hSupp).
  rewrite (@top_current_boundary_coordinate R h2 p U hU T j) current_value_scale in hAction.
  have hSign:(-1:R)^+p.+1!=0 by rewrite expf_neq0 ?oppr_eq0 ?oner_eq0.
  by move/eqP:hAction;rewrite mulf_eq0 (negbTE hSign) orFb;move=>/eqP.
have hAgree:forall psi:@current_test_space R h2 p.+1 U hU p.+1,
    @current_test_support R h2 p.+1 p.+1 U hU psi `<=` A ->
    @current_value R h2 p.+1 U hU p.+1 D psi=
      @current_value R h2 p.+1 U hU p.+1 0 psi.
  move=>psi hPsi;by rewrite (hZero psi hPsi) linear0 hom_zeroE.
have h:=@current_support_difference_agreement R h2 p.+1 p.+1 U hU D 0 A hA hAgree.
by rewrite subr0 in h.
Qed.
