(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    the actual leading Taylor polynomial of any original
    representative has the printed negligible remainder. Actual
    germ jets, local differential uniqueness and the preceding
    compact-uniform Taylor theorem supply the connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormClassOneUP NormSmoothFields NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherDifferentialUnique ContinuousMultilinearUP ContinuousMultilinearSealed
  NormAnalyticUP HolomorphicGermUP HolomorphicGermRepresentatives HolomorphicGermJetsSealed
  HolomorphicInitialPolynomialUP LeadingVectorTaylorRemainder HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Remainder.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variable NX:X->R.
Variable hNX:@is_real_norm R XR NX.
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i XR CR NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i XR CR NX N hNX hN).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i XR CR NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i XR CR NX N hNX hN).

(** Source for [holomorphic_initial_taylor_remainder]: the
    first remainder display of 3.4.12, p. 339, extending 3.4.11, p. 338,
    for every actual representative of the original germ.
    The estimate includes zero increments and retains the
    original degree and factorial normalization. *)
Theorem holomorphic_initial_taylor_remainder
    (alpha:holomorphic_germ_space hNX (0:X)) k (P:X->ComplexScalars.C R)
    (f:@holomorphic_representative_type R X NX hNX 0):
  is_initial_holomorphic_germ_polynomial alpha k P ->holomorphic_germ f=alpha ->
  @is_homogeneous_polynomial R XR CR k P /\
  @norm_class_zero R XR CR NX N setT P /\
  (forall (t:R) v,P (t*:(v:XR))=t^+k*:(P v:CR)) /\
  forall e:R,0<e ->exists r:R,0<r /\forall x,NX x<r ->
    N (holomorphic_representative_value f x-P x)<=e*(NX x)^+k.
Proof.
move=>[hPositive [hTop [hLower hFormula]]] hGerm.
case:k hPositive hTop hLower hFormula=>[|k] // hPositive hTop hLower hFormula.
have [U [ha hHOL]]:=holomorphic_representative_holomorphic f.
have [V [c [hV0 [hVU [hClass hBound]]]]]:=hHOL.1 0 ha.
pose U0:=U.
have hUT:V `<=` setT by move=>x _.
have [D hD]:=@norm_smooth_fields_exist R XR CR NX N hNX hN V
  (holomorphic_representative_value f) hClass.
have hOpen x (hx:V x):@norm_domain_interior R XR NX V x:=((hClass 0%N).1 x hx).1.
have hJet i:D i 0=@HolomorphicGermJets.value R X NX hNX 0 i alpha.
  have hFull:=(@norm_higher_differential_open_restriction R XR CR NX N hNX hN
    Z ev ZN hZ i setT V (holomorphic_representative_value f) hUT hOpen 0 hV0 (D i 0)).2
    ((hD i).1 0 hV0).
  exact:(@norm_higher_differential_unique R XR CR NX N hNX hN Z ev ZN hZ
    setT (holomorphic_representative_value f) i 0 _ _ hFull
    (@HolomorphicGermJets.laws R X NX hNX 0 i alpha f hGerm)).
have hDLower i (hi:(i<k.+1)%N):D i 0=0 by rewrite hJet (hLower i hi).
have hTaylor:=@leading_vector_actual_taylor_remainder R XR CR NX hNX N hN V
  (holomorphic_representative_value f) D k hV0 (fun i hi=>(hD i).1) (hD k.+1).2 hDLower.
have hP:(fun v=>((k.+1)`!)%:R^-1*:@ev k.+1 [ffun _=>v] (D k.+1 0))= P.
  apply:funext=>v;by rewrite hJet hFormula.
have hValues v:((k.+1)`!)%:R^-1*:@ev k.+1 [ffun _=>v] (D k.+1 0)= P v.
  exact:(congr1 (fun g=>g v) hP).
rewrite hP in hTaylor.
have [hPolynomial [hContinuous [hScale hRemainder]]]:=hTaylor.
split;first exact:hPolynomial.
split;first exact:hContinuous.
split;first by move=>t v;rewrite -!hValues;exact:hScale.
move=>e he;have [r [hr hR]]:=hRemainder e he.
exists r;split;first exact:hr.
move=>x hx;rewrite -hValues;exact:(hR x hx).2.
Qed.
End Remainder.
