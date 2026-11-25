(** Federer (1969), 4.1.19, p. 377: every
    original class-one form and its actual exterior
    derivative obey the printed weak equation. Localize
    with the earlier class-one replacement only inside
    the proof; the derivative may be unbounded on U. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP
  NormDifferentialLocal NormClassOneUP NormRegularity
  NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingPairing PairingLinear ExteriorDerivativeUP
  CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet SmoothFunctionSupport SmoothCurrentDivergence
  CurrentCompactSmoothDivergenceSupport CurrentClassOneCutoff
  CurrentWeakExteriorPairUP CompactContinuousCurrentFormBounded
  CurrentClassOneWeakExteriorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ClassOneWeakEquation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation hN d := (@current_form_comass_real_norm R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).

(** Source for [current_class_one_exterior_weak_integral]:
    the integration-by-parts direction of the
    class-one parenthesis in Federer 4.1.19,
    p. 377. Both original fields retain
    their full U-domain; no boundedness of
    the derivative, finite volume of U,
    or compact support of phi is imposed. *)
Theorem current_class_one_exterior_weak_integral
    (phi : X -> Y m) (beta : X -> Y m.+1) :
  norm_class hNX (hN m) U phi 1%N ->
  (forall x, U x -> has_exterior_derivative NX (N m) U phi x (beta x)) ->
  @is_weak_current_exterior_pair R h2 n m U hU
    (fun x : UT => phi (set_val x))
    (fun x : UT => beta (set_val x)).
Proof.
move=> hClass hActual eta K hSupport.
have [C [chi [b [hChi [hB [hExterior [hOff
    [W [hW [hKW [hWU hAgreement]]]]]]]]]]] :=
  @current_class_one_compact_replacement R h2 n m U hU K phi beta hClass hActual.
have hChiU : norm_class hNX (hN m) U chi 1%N.
  exact: (@norm_class_open_restriction R X (Y m) NX (N m) hNX (hN m)
    setT U chi 1%N (fun _ _ => Logic.I) hU hChi).
have hBClass := (@norm_class_zeroP R X (Y m.+1) NX (N m.+1)
  hNX (hN m.+1) setT b).2 hB.
have hBClassU := @norm_class_open_restriction R X (Y m.+1) NX (N m.+1)
  hNX (hN m.+1) setT U b 0%N (fun _ _ => Logic.I) hU hBClass.
have hBU := norm_class_continuous hBClassU.
have hExteriorU (x : X) (hx : U x) :
    has_exterior_derivative NX (N m) U chi x (b x).
  have [L [hL hValue]] := hExterior x.
  exists L; split; last exact: hValue.
  exact: (@norm_differential_restrict R X (Y m) NX (N m) setT U chi x L
    (fun _ _ => Logic.I) (@hU x hx) hL).
have hChiBounded := @compact_continuous_current_form_bounded R h2 n m U hU
  C chi (norm_class_continuous hChiU) (fun x _ hx => (hOff x hx).1).
have hBBounded := @compact_continuous_current_form_bounded R h2 n m.+1 U hU
  C b hBU (fun x _ hx => (hOff x hx).2).
have hIntegral := @current_class_one_bounded_exterior_weak_integral R h2 n m U hU
  chi b hChiU hExteriorU hChiBounded hBBounded eta K hSupport.
have hDivSupport := @current_compact_smooth_divergence_support R h2 n m
  U hU K eta hSupport.
have hPoint : (fun x : UT =>
    pairing (ev m (div eta) (set_val x)) (chi (set_val x))+
    pairing (ev m.+1 eta (set_val x)) (b (set_val x)))=
    (fun x : UT =>
    pairing (ev m (div eta) (set_val x)) (phi (set_val x))+
    pairing (ev m.+1 eta (set_val x)) (beta (set_val x))).
  apply: funext=> x.
  have [hx|hx] := pselect (smooth_compact_carrier K (set_val x)).
  - have [hPhi hBeta] := @hAgreement (set_val x) (@hKW (set_val x) hx).
    by rewrite hPhi hBeta.
  - have hEta := (smooth_function_compact_support_iff (hE m.+1) K eta).1
      hSupport (set_val x) hx.
    have hDiv := (smooth_function_compact_support_iff (hE m) K (div eta)).1
      hDivSupport (set_val x) hx.
    by rewrite hEta hDiv /pairing !linear0.
by rewrite hPoint in hIntegral.
Qed.
End ClassOneWeakEquation.
