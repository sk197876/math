(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: the independently specified coefficient sequences are
    realised by actual holomorphic germs. Reuse the proved original
    complex form-series theorem and exact derivative operator norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology constructive_ereal.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  SymmetricForms SymmetricOperatorNorm MultilinearTupleForm ContinuousMultilinearSymmetricNorm
  ContinuousSymmetricFormAdapter ContinuousMultilinearUP ContinuousMultilinearSealed
  ComplexMultilinearFromReal HolomorphicFormalJetUP HolomorphicFormSeries AnalyticJetMajorant
  HolomorphicGermUP HolomorphicGermJetsSealed.
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
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNXR hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNXR hN).
Local Notation NZ:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNXR hN).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m XR CR NX N hNXR hN).

(** Source for [holomorphic_formal_jet_realisation]: actual symmetry,
    complex scalar equations and the printed bounds supply an
    original holomorphic germ with exactly the prescribed jets,
    extending 3.4.5, p. 319. Realisation is not a premise. *)
Theorem holomorphic_formal_jet_realisation a s t (w:forall m,Z m):
  @is_holomorphic_formal_jet R X NX hNX s t w ->exists alpha:holomorphic_germ_space hNXR a,
    forall m,@HolomorphicGermJets.value R X NX hNXR a m alpha=w m.
Proof.
move=>hw.
have hComplex m:=@complex_multilinear_from_real R X C^o m (fun u=>ev m u (w m))
  (continuous_multilinear_evaluation (hZ m) (w m)) (@holomorphic_formal_jet_complex R X NX hNX s t w hw m).
have hCF m:exists F:S_m X C^o m,forall u,F u=ev m [ffun i=>tnth u i] (w m).
  exact:(@symmetric_multilinear_tuple_form_exists C X C^o m (fun u=>ev m u (w m))
    (hComplex m) (@holomorphic_formal_jet_symmetric R X NX hNX s t w hw m)).
have hRF m:exists P:S_m XR CR m,forall u,P u=ev m [ffun i=>tnth u i] (w m).
  exact:(@symmetric_multilinear_tuple_form_exists R XR CR m (fun u=>ev m u (w m))
    (continuous_multilinear_evaluation (hZ m) (w m)) (@holomorphic_formal_jet_symmetric R X NX hNX s t w hw m)).
pose F m:=projT1 (cid (hCF m)).
have hF m:=projT2 (cid (hCF m)).
pose P m:=projT1 (cid (hRF m)).
have hP m:=projT2 (cid (hRF m)).
have hValues m u:P m u=F m u by rewrite hP hF.
have hNorm m:@symmetric_operator_norm R XR CR NX hNXR.1 N m (P m)=(NZ m (w m))%:E.
  exact:(@continuous_multilinear_symmetric_norm R m XR CR (Z m) NX N hNXR hN
    (ev m) (NZ m) (hZ m) (w m) (P m) (hP m)).
have hBound m:@norm_bounded_symmetric_form R m XR CR NX N (P m).
  apply:(@finite_operator_norm_sform_bounded R m XR CR NX N hNXR hN (P m)
    (s%:R*t%:R^+m*(m`!)%:R)).
  rewrite hNorm lee_fin;exact:@holomorphic_formal_jet_growth R X NX hNX s t w hw m.
pose c:=((s%:R+1)*(t%:R+1):R).
have hS:0<=(s%:R:R):=ler0n R s.
have hT:0<=(t%:R:R):=ler0n R t.
have hc:0<c by rewrite /c mulr_gt0 // addrC ltr_pwDl.
have hGrowth m (hm:(1<=m)%N):(@symmetric_operator_norm R XR CR NX hNXR.1 N m (P m)<=
    (c^+m*(m`!)%:R)%:E)%E.
  rewrite hNorm lee_fin.
  apply:le_trans (@holomorphic_formal_jet_growth R X NX hNX s t w hw m) _.
  exact:(@analytic_factorial_growth_majorant R s%:R t%:R m hS hT hm).
have [alpha hAlpha]:=@holomorphic_form_series_realisation R X NX hNX F P a c hValues hc hBound hGrowth.
exists alpha=>m;apply:(continuous_multilinear_extensional (hZ m))=>u.
have hh:=hAlpha m [tuple u j|j<m].
rewrite hF in hh.
have hTuple:[ffun i=>tnth [tuple u j|j<m] i]=u.
  by apply/ffunP=>i;rewrite ffunE tnth_mktuple.
by rewrite hTuple in hh.
Qed.
End Realisation.
