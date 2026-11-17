(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: complex symmetric coefficient forms with real
    factorial bounds have actual holomorphic germ realisations.
    Reuse the original proved complex form-series theorem and
    the existing numerical majorant; retain every prescribed coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  SymmetricForms SymmetricOperatorNorm ContinuousSymmetricFormAdapter AnalyticJetMajorant
  ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermRing HolomorphicGermJetsSealed HolomorphicFormSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Realisation.
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

(** Source for [holomorphic_form_growth_realisation]: actual original
    complex forms with bounds S*T^m*m! are realised by original
    germ derivatives, extending 3.4.5, p. 319. All
    nonnegative S and T and degree zero remain. *)
Theorem holomorphic_form_growth_realisation a (F:forall m,S_m X C^o m)
    (P:forall m,S_m XR CR m) (S T:R):
  (forall m u,P m u=F m u) ->0<=S ->0<=T ->
  (forall m,(@symmetric_operator_norm R XR CR NX hNXR.1 N m (P m)<=
    (S*T^+m*(m`!)%:R)%:E)%E) ->
  exists alpha:@holomorphic_germ_ring R X NX hNXR a,forall m u,
    @ContinuousMultilinear.evaluation R m XR CR NX N hNXR hN u
      (@HolomorphicGermJets.value R X NX hNXR a m alpha)=F m [tuple u i|i<m].
Proof.
move=>hValues hS hT hBound.
pose c:=(S+1)*(T+1).
have hc:0<c by rewrite /c mulr_gt0 // addrC ltr_pwDl.
have hFinite m:@norm_bounded_symmetric_form R m XR CR NX N (P m).
  exact:(@finite_operator_norm_sform_bounded R m XR CR NX N hNXR hN (P m) _ (hBound m)).
have hGrowth m (hm:(1<=m)%N):(@symmetric_operator_norm R XR CR NX hNXR.1 N m (P m)<=
    (c^+m*(m`!)%:R)%:E)%E.
  apply:le_trans (hBound m) _;rewrite lee_fin.
  exact:(@analytic_factorial_growth_majorant R S T m hS hT hm).
have [alpha hAlpha]:=@holomorphic_form_series_realisation R X NX hNX F P a c hValues hc hFinite hGrowth.
exists alpha=>m u.
have hh:=hAlpha m [tuple u i|i<m].
have hTuple:[ffun j=>tnth [tuple u i|i<m] j]=u.
  by apply/ffunP=>j;rewrite ffunE tnth_mktuple.
by rewrite hTuple in hh.
Qed.
End Realisation.
