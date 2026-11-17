(** Federer (1969), 3.4.12, p. 339, extending 3.4.6,
    pp. 321–322: an exact original complex line value a*t^k
    with a nonzero proves actual positive directional order.
    Reuse the normed-target real line Taylor uniqueness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormRegularity NormHigherDifferentialUP NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermJetsSealed
  HolomorphicGermFormsUP HolomorphicGermFormsSealed AnalyticDirectionalCoefficient
  AnalyticDirectionalPolynomialLine ComplexWeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Lines.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i XR CR NX N hNXR hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i XR CR NX N hNXR hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i XR CR NX N hNXR hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i XR CR NX N hNXR hN).

(** Source for [complex_weierstrass_line_regularity]: the original
    holomorphic representative has order k along v if its
    exact complex line values are a*t^k, extending 3.4.6,
    pp. 321–322. Every derivative assertion is proved. *)
Theorem complex_weierstrass_line_regularity (f:holomorphic_representative_type hNXR (0:X)) k (v:X) (a:C):
  (0<k)%N ->a!=0 ->(forall t:C,holomorphic_representative_value f (t*:v)=a*t^+k) ->
  is_complex_weierstrass_regular_germ hNX (holomorphic_germ f) k v.
Proof.
move=>hK hA hLine.
pose F:=holomorphic_representative_value f.
pose alpha:=holomorphic_germ f.
have [U [ha [hf _]]]:=holomorphic_representative_holomorphic f.
have hOpen x (hx:U x):@norm_domain_interior R XR NX U x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have hDirectional i:((i`!)%:R:R)^-1*:(ev i [ffun _:'I_i=>v]
    (@HolomorphicGermJets.value R X NX hNXR 0 i alpha):CR)=if (i==k)%N then a else 0.
  have [c [hc _]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN U F i v hf.
  have hExact t (ht:`|t|<1):F ((0:XR)+t*:(v:XR))=
      \sum_(n<k.+1) t^+n*:(if ((n:nat)==k)%N then (a:CR) else 0).
    rewrite add0r /F hLine (bigD1 (Ordinal (ltnSn k))) //= eqxx.
    have hOthers:(\sum_(n<k.+1 | n!=Ordinal (ltnSn k))
        t^+n*:(if ((n:nat)==k)%N then (a:CR) else 0))=0.
      apply:big1=>n hn.
      have hNe:((n:nat)!=k)%N by move:hn;rewrite -val_eqE /=.
      by rewrite (negbTE hNe) scaler0.
    rewrite hOthers addr0.
    change (a*(ComplexScalars.embed R t)^+k=ComplexScalars.embed R (t^+k)*a).
    by rewrite rmorphXn mulrC.
  have hFinite:=@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN
    U F i v 0 c k.+1 (fun n=>if (n==k)%N then a else 0) 1 ha hf hc ltr01 hExact.
  have hJet:=@HolomorphicGermJets.laws R X NX hNXR 0 i alpha f (erefl _).
  have hLocal:=(@norm_higher_differential_open_restriction R XR CR NX N hNXR hN Z ev NZ hZ
    i setT U F (fun x _=>Logic.I) hOpen 0 ha (@HolomorphicGermJets.value R X NX hNXR 0 i alpha)).1 hJet.
  have hAt:=hc 0 ha (@HolomorphicGermJets.value R X NX hNXR 0 i alpha) hLocal.
  change (c 0=((i`!)%:R:R)^-1*:(ev i [ffun _:'I_i=>v]
    (@HolomorphicGermJets.value R X NX hNXR 0 i alpha):CR)) in hAt.
  rewrite -hAt hFinite.
  case hSmall:(i<k.+1)%N=>//.
  have hNe:(i!=k)%N by apply/eqP=>h;by rewrite h ltnSn in hSmall.
  by rewrite (negbTE hNe).
have hTuple i:[ffun j=>tnth [tuple v|_<i] j]=[ffun _:'I_i=>v].
  by apply/ffunP=>j;rewrite !ffunE tnth_mktuple.
split;first exact:hK.
split.
- move=>i hi.
  rewrite (@HolomorphicGermForms.laws R X NX hNX 0 i alpha) hTuple.
  have hNe:(i!=k)%N by apply/eqP=>h;by rewrite h ltnn in hi.
  have hValue:=hDirectional i;rewrite (negbTE hNe) in hValue.
  have hFact:((i`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
  apply/eqP;move/eqP:hValue;by rewrite scaler_eq0 invr_eq0 (negbTE hFact) orFb.
- move=>hZero.
  rewrite (@HolomorphicGermForms.laws R X NX hNX 0 k alpha) hTuple in hZero.
  have hValue:=hDirectional k;rewrite hZero scaler0 eqxx in hValue.
  by rewrite -hValue eqxx in hA.
Qed.
End Lines.
