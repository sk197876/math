(** Supporting Federer (1969), 3.4.8(5), p. 328:
    actual analytic radial Taylor quotients exist
    uniquely. The proved derivative-growth cover and
    contraction bound supply actual analytic coefficients.
    Taylor injectivity proves uniqueness. No quotient
    or finite-jet power relation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricOperatorNorm PolynomialTaylorTerms
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermRing
  AnalyticGermJetsSealed AnalyticGermCoefficientForms AnalyticGermGrowthUP
  AnalyticGermGrowthSealed AnalyticGermGrowthCover AnalyticGermTaylorInjective
  AnalyticFormGrowthRealisation AnalyticRadialQuotientUP RadialTaylorFormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_radial_quotient_exists]: every
    original germ and vector have an actual analytic
    quotient with the independently specified derivative
    equations. This expands 3.1.24, pp. 238–239,
    for the closedness proof of 3.4.8(5), p. 328. *)
Theorem analytic_radial_quotient_exists (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) (v:X):
  exists q:@analytic_germ_ring R X NX hNX a,is_analytic_radial_quotient alpha v q.
Proof.
have [phi [hPhi [hPhiBound hPhiNorm]]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a alpha.
have [s [t [_ [_ hGrowth]]]]:=@analytic_germ_positive_growth_cover R X NX hNX a alpha.
have hBound m:(symmetric_operator_norm hNX.1 (fun z:R^o=>`|z|%R) (phi m)
    <=(s%:R*t%:R^+m*(m`!)%:R)%:E)%E.
  rewrite hPhiNorm lee_fin.
  exact:(@analytic_germ_growth_membership R X NX hNX a s t _
    (@AnalyticGermGrowth.laws R X NX hNX a s t) alpha).1 hGrowth m.
pose psi m:=((m.+1)%:R:R)^-1*:symmetric_taylor_term m (phi m.+1) v.
have hPsiBound:=@radial_taylor_form_factorial_bound R X NX hNX phi s%:R t%:R v
  (ler0n R s) (ler0n R t) hBound.
have hS:0<=s%:R*t%:R*NX v.
  exact:mulr_ge0 (mulr_ge0 (ler0n R s) (ler0n R t)) (real_seminorm_nonnegative hNX.1 v).
have [q hQ]:=@analytic_form_growth_realisation R X NX hNX a psi (s%:R*t%:R*NX v) t%:R
  hS (ler0n R t) hPsiBound.
exists q=>m F hF u.
have hEqual:F = phi m.+1.
  apply:sform_ext=>w;by rewrite hF hPhi.
by rewrite hEqual hQ /psi sform_scaleE.
Qed.

(** Source for [analytic_radial_quotient_unique]: the
    original derivative equations determine every quotient
    jet, hence its actual analytic germ. This
    supports the same expanded Taylor argument for
    3.4.8(5), p. 328. *)
Lemma analytic_radial_quotient_unique (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a
  (alpha:@analytic_germ_ring R X NX hNX a) (v:X)
  (q r:@analytic_germ_ring R X NX hNX a):
  is_analytic_radial_quotient alpha v q ->is_analytic_radial_quotient alpha v r ->q = r.
Proof.
move=>hq hr.
have [phi [hPhi _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a alpha.
apply:(@analytic_germ_jets_injective R X NX hNX a q r)=>m.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R m X R^o NX
  (fun z=>`|z|%R) hNX (@scalar_absolute_value_norm R)))=>u.
by rewrite (hq m (phi m.+1) (hPhi m.+1)) (hr m (phi m.+1) (hPhi m.+1)).
Qed.
