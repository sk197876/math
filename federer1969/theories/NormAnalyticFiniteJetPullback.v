(** Federer (1969), 3.4.5, pp. 318–321: finite
    jets under actual analytic substitutions, supporting the
    local algebra and the cited counterexample. The proof
    uses the actual Taylor remainder of 3.1.11, p. 222. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP PolynomialFunctions ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticOperations
  NormAnalyticComposition NormJetUP NormJetCompositionRemainder NormLittleOPower NormFiniteJetAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_finite_jet_pullback]: replacing
    an actual analytic outer map by its actual kth
    Taylor jet preserves every differential through order k
    after an actual analytic substitution, supporting 3.4.5,
    pp. 318–321. The finite polynomial's actual analyticity
    is explicit, and is separately proved for the finite-dimensional
    scalar case; no agreement conclusion is assumed. *)
Theorem norm_analytic_finite_jet_pullback (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    (A:set X) (B:set Y) (f:X->Y) (g:Y->T) k a (P:PolynomialFunction Y T):
  (1<=k)%N ->A a ->B (f a) ->
  @norm_analytic R X Y NX NY hNX hNY A f ->
  @norm_analytic R Y T NY NT hNY hNT B g ->
  @norm_analytic R Y T NY NT hNY hNT setT P ->
  is_norm_jet_polynomial NY
    (fun i=>@ContinuousMultilinear.evaluation R i Y T NY NT hNY hNT)
    (fun i=>@ContinuousMultilinear.norm R i Y T NY NT hNY hNT) B g k (f a) P ->
  norm_finite_jet_agreement NX
    (fun i=>@ContinuousMultilinear.evaluation R i X T NX NT hNX hNT)
    (fun i=>@ContinuousMultilinear.norm R i X T NX NT hNX hNT)
    (fun x=>A x /\B (f x)) A (fun x=>g (f x)) (fun x=>P (f x)) k a.
Proof.
move=>hk ha hb hf hg hPolynomial hP.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ez i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose NZ i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
pose W i:=@ContinuousMultilinear.space R i Y T NY NT hNY hNT.
pose ew i:=@ContinuousMultilinear.evaluation R i Y T NY NT hNY hNT.
pose NW i:=@ContinuousMultilinear.norm R i Y T NY NT hNY hNT.
pose hW i:=@ContinuousMultilinear.laws R i Y T NY NT hNY hNT.
pose U i:=@ContinuousMultilinear.space R i X T NX NT hNX hNT.
pose eu i:=@ContinuousMultilinear.evaluation R i X T NX NT hNX hNT.
pose NU i:=@ContinuousMultilinear.norm R i X T NX NT hNX hNT.
pose hU i:=@ContinuousMultilinear.laws R i X T NX NT hNX hNT.
have hComposite:=norm_analytic_composition hf hg.
have hCompositeP:=norm_analytic_compose_on (fun x (_:A x)=>Logic.I) hf hPolynomial.
apply:(@norm_radial_remainder_finite_jet_agreement R X T NX NT hNX hNT U eu NU hU
  (fun x=>A x /\B (f x)) A (fun x=>g (f x)) (fun x=>P (f x)) k a
  (conj ha hb) ha (norm_analytic_class_all_orders hComposite k)
  (norm_analytic_class_all_orders hCompositeP k))=>v.
exact:(@norm_outer_jet_pullback_remainder R X Y T NX NY NT hNX hNY hNT
  Z W ez NZ ew NW hZ hW A B f g k a P hk ha hb
  (norm_analytic_class_all_orders hf k) (norm_analytic_class_all_orders hg k) hP v).
Qed.
