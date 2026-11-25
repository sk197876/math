(** Federer (1969), 4.1.19, p. 377: a
    pointwise exterior equation on the valid kernel
    locus gives the weak integral for every test
    supported there. This supporting restriction step uses
    only the original class-one integration-by-parts law. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormOpenDomainLaws NormBoundedLinearTopology NormClassOneUP NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing PairingLinear CurrentDomain
  CurrentCoefficientNorms CurrentVectorSpaces SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothCurrentDivergence
  CurrentLipschitzCompactImage ClosedBallContainmentOpen EuclideanClosedSupportTube
  VectorSetSum CompactContinuousVectorZeroExtension CurrentClassOneWeakExterior
  WeakExteriorFullCompactTest ExteriorDerivativeUP EuclideanLebesgueDimensions
  MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothWeakTest.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation V d := (exterior_power X d).
Local Notation Y d := (A_m X R^o d).
Local Notation YN d := (@current_form_comass R h2 n d).
Local Notation hYN d := (@current_form_comass_real_norm R h2 n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation E d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation ev d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation DT d := (smooth_test_space (hE d)).
Local Notation tv d := (smooth_test_value (hE d)).
Local Notation div := (@smooth_current_divergence R h2 n m Full hFull).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.

(** Source for [current_smooth_weak_test_on_kernel_locus]:
    the interior-domain weak integral in the
    converse smoothing argument of Federer 4.1.19,
    p. 377. The support tube premise is
    discharged internally by its final consumer for
    all sufficiently small positive radii. *)
Theorem current_smooth_weak_test_on_kernel_locus
    (K : smooth_compact_set hNX U) (a : DT m) (b : DT m.+1)
    (epsilon : R) (g : X -> Y m) (h : X -> Y m.+1) :
  0<epsilon ->
  @euclidean_closed_support_tube R n (smooth_compact_carrier K) epsilon `<=` U ->
  tv m a=ev m (div (smooth_test_inclusion (hE m.+1) b)) ->
  (forall x, ~smooth_compact_carrier K x -> tv m a x=0 /\ tv m.+1 b x=0) ->
  norm_class hNX (hYN m) Full g 1%N ->
  (forall x, norm_closed_ball_containment U epsilon x ->
    has_exterior_derivative NX (YN m) U g x (h x)) ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x => pairing (tv m a x) (g x)+
      pairing (tv m.+1 b x) (h x))) 0%E.
Proof.
move=> hEpsilon hInside hDiv hOff hClass hExterior.
pose A := norm_closed_ball_containment U epsilon.
have hOpenU : @open XT U.
  rewrite openE=> x hx; exact: (norm_domain_interior_neighbourhood hNX U x).1 (@hU x hx).
have hOpenA := @closed_ball_containment_open R n U epsilon hOpenU.
have hA (x : X) (hx : A x) : norm_domain_interior NX A x.
  apply: (norm_domain_interior_neighbourhood hNX A x).2.
  move: hOpenA; rewrite openE; exact.
have hAU (x : X) (hx : A x) : U x.
  apply: hx; rewrite subrr (real_seminorm_zero hNX.1); exact: ltW hEpsilon.
have hKA : smooth_compact_carrier K `<=` A.
  move=> x hx y hy.
  have hN : NX (y-x)<=epsilon by rewrite (real_seminorm_subtract hNX.1).
  have hMember := @vector_set_sum_contains X (smooth_compact_carrier K)
    [set v : X | NX v<=epsilon] x (y-x) hx hN.
  have hTube : @euclidean_closed_support_tube R n (smooth_compact_carrier K)
      epsilon (x+(y-x)) := hMember.
  rewrite addrC subrK in hTube; exact: (@hInside y hTube).
pose KA := @Build_smooth_compact_set R X NX hNX A (smooth_compact_carrier K)
  hKA (smooth_compact_is_compact K).
pose KF := @current_compact_index_in_open R n U Full K (fun _ _ => Logic.I).
pose eta := smooth_test_inclusion (hE m.+1) b.
have hSupport : @smooth_function_support R X (V m.+1) NX hNX Full
    (E m.+1) (ev m.+1) eta `<=` smooth_compact_carrier KF.
  apply: (smooth_function_compact_support_iff (hE m.+1) KF eta).2=> x hx.
  exact: (@hOff x hx).2.
have hClassA := @norm_class_open_restriction R X (Y m) NX (YN m)
  hNX (hYN m) Full A g 1%N (fun _ _ => Logic.I) hA hClass.
have hExteriorA (x : X) (hx : A x) : has_exterior_derivative NX (YN m) A g x (h x).
  have [L [hL hValue]] := @hExterior x hx.
  exists L; split; last exact: hValue.
  exact: (@norm_differential_restrict R X (Y m) NX (YN m) U A g x L
    hAU (@hA x hx) hL).
have hWeakA := @current_class_one_exterior_weak_integral R h2 n m A hA
  g h hClassA hExteriorA.
have hIntegral := @weak_current_exterior_full_compact_test R h2 n m A hA
  (fun x : current_domain R n A => g (set_val x))
  (fun x : current_domain R n A => h (set_val x)) KA eta hWeakA hSupport.
have hFunction : (fun x =>
      pairing (ev m (div eta) x)
        (@compact_vector_open_extension R XT A (Y m)
          (fun y : current_domain R n A => g (set_val y)) x)+
      pairing (ev m.+1 eta x)
        (@compact_vector_open_extension R XT A (Y m.+1)
          (fun y : current_domain R n A => h (set_val y)) x))=
    (fun x => pairing (tv m a x) (g x)+pairing (tv m.+1 b x) (h x)).
  apply: funext=> x; rewrite -hDiv.
  case: (pselect (smooth_compact_carrier K x))=> hx.
  - pose p : current_domain R n A := exist _ x (mem_set (@hKA x hx)).
    change (pairing (tv m a (set_val p))
        (@compact_vector_open_extension R XT A (Y m)
          (fun y : current_domain R n A => g (set_val y)) (set_val p))+
      pairing (tv m.+1 b (set_val p))
        (@compact_vector_open_extension R XT A (Y m.+1)
          (fun y : current_domain R n A => h (set_val y)) (set_val p))=
      pairing (tv m a (set_val p)) (g (set_val p))+
      pairing (tv m.+1 b (set_val p)) (h (set_val p))).
    by rewrite !compact_vector_open_extension_value.
  - change (pairing (tv m a x)
        (@compact_vector_open_extension R XT A (Y m)
          (fun y : current_domain R n A => g (set_val y)) x)+
      pairing (tv m.+1 b x)
        (@compact_vector_open_extension R XT A (Y m.+1)
          (fun y : current_domain R n A => h (set_val y)) x)=
      pairing (tv m a x) (g x)+pairing (tv m.+1 b x) (h x)).
    by rewrite (@hOff x hx).1 (@hOff x hx).2
      !(bil0l (@pairing_bilinear R X R^o m))
      !(bil0l (@pairing_bilinear R X R^o m.+1)).
by rewrite hFunction in hIntegral.
Qed.
End SmoothWeakTest.
