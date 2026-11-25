(** Federer (1969), 3.4.12, p. 339, extending the
    ideal-closedness argument of 3.4.8(5), p. 328: actual
    holomorphic radial quotients exist uniquely. Reuse the original
    complex forms, normed-target contraction bound and proved
    holomorphic form-series realisation; no quotient is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  SymmetricForms SymmetricOperatorNorm PolynomialTaylorTerms ContinuousMultilinearUP ContinuousMultilinearSealed
  ComplexSymmetricTaylorRestriction NormRadialTaylorFormBound HolomorphicFormGrowthRealisation
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  HolomorphicGermRealCoefficientForms HolomorphicGermJetGrowth HolomorphicGermTaylorInjective HolomorphicRadialQuotientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Quotients.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNXR hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNXR hN).
Local Notation NZ:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNXR hN).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m XR CR NX N hNXR hN).

(** Source for [holomorphic_radial_quotient_exists]: each original
    holomorphic germ and vector have an actual quotient satisfying
    the independently stated derivative equations, expanding Taylor's
    formula for 3.4.8(5), p. 328, over the complex field. *)
Theorem holomorphic_radial_quotient_exists a (alpha:@holomorphic_germ_ring R X NX hNXR a) v:
  exists q:@holomorphic_germ_ring R X NX hNXR a,
    @is_holomorphic_radial_quotient R X NX hNX a alpha v q.
Proof.
pose phi m:=@HolomorphicGermForms.value R X NX hNX a m alpha.
have [P [hP [hPBound hPNorm]]]:=@holomorphic_germ_coefficient_forms_exists R X NX hNXR a alpha.
have hValues m t:P m t=phi m t.
  by rewrite /phi (@HolomorphicGermForms.laws R X NX hNX a m alpha) hP.
have [b [c [hb [hc hGrowth]]]]:=@holomorphic_germ_positive_jet_growth R X NX hNX a alpha.
have hBound m:(@symmetric_operator_norm R XR CR NX hNXR.1 N m (P m)<=
    (b*c^+m*(m`!)%:R)%:E)%E.
  rewrite hPNorm lee_fin;exact:hGrowth m.
pose psi m:=((m.+1)%:R:C)^-1*:symmetric_taylor_term m (phi m.+1) v.
pose Q m:=((m.+1)%:R:R)^-1*:symmetric_taylor_term m (P m.+1) v.
have hQValues m t:Q m t=psi m t.
  rewrite /Q /psi !sform_scaleE
    (@complex_symmetric_taylor_restriction R X C^o m.+1 (phi m.+1) (P m.+1) (hValues m.+1) m v t).
  change (ComplexScalars.embed R (((m.+1)%:R:R)^-1)*symmetric_taylor_term m (phi m.+1) v t=
    ((m.+1)%:R:C)^-1*symmetric_taylor_term m (phi m.+1) v t).
  by rewrite fmorphV rmorph_nat.
have hQBound:=@norm_radial_taylor_form_factorial_bound R XR CR NX N hNXR hN P b c v
  (ltW hb) (ltW hc) hBound.
have hS:0<=b*c*NX v:=mulr_ge0 (mulr_ge0 (ltW hb) (ltW hc)) (real_seminorm_nonnegative hNXR.1 v).
have [q hQ]:=@holomorphic_form_growth_realisation R X NX hNX a psi Q (b*c*NX v) c
  hQValues hS (ltW hc) hQBound.
exists q=>m F hF u.
have hEqual:F=phi m.+1.
  apply:sform_ext=>t;by rewrite hF /phi (@HolomorphicGermForms.laws R X NX hNX a m.+1 alpha).
by rewrite hQ /psi hEqual.
Qed.

(** Source for [holomorphic_radial_quotient_unique]: the actual
    derivative equations determine every quotient jet and hence
    its original germ, supporting the expanded complex
    ideal-power argument for 3.4.8(5), p. 328. *)
Lemma holomorphic_radial_quotient_unique a (alpha:@holomorphic_germ_ring R X NX hNXR a) v
    (q r:@holomorphic_germ_ring R X NX hNXR a):
  @is_holomorphic_radial_quotient R X NX hNX a alpha v q ->
  @is_holomorphic_radial_quotient R X NX hNX a alpha v r ->q=r.
Proof.
move=>hq hr.
apply:(@holomorphic_germ_jets_injective R X NX hNXR a q r)=>m.
apply:(continuous_multilinear_extensional (hZ m))=>u.
pose F:=@HolomorphicGermForms.value R X NX hNX a m.+1 alpha.
have hF:=@HolomorphicGermForms.laws R X NX hNX a m.+1 alpha.
by rewrite (hq m F hF u) (hr m F hF u).
Qed.
End Quotients.
