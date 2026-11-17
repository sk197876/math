(** Federer (1969), 3.4.11, p. 338:
    the actual leading Taylor polynomial of any original
    representative has the printed negligible remainder. Actual
    germ jets, local differential uniqueness and the preceding
    compact-uniform Taylor theorem supply the connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormClassOneUP NormSmoothFields NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherDifferentialUnique ContinuousMultilinearUP ContinuousMultilinearSealed
  NormAnalyticUP AnalyticGermUP AnalyticGermRepresentatives AnalyticGermJetsSealed
  AnalyticInitialPolynomialUP LeadingTaylorRemainder HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Remainder.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X R^o NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X R^o NX N hNX hN).

(** Source for [analytic_initial_taylor_remainder]: the
    first remainder display of 3.4.11, p. 338,
    for every actual representative of the original germ.
    The estimate includes zero increments and retains the
    original degree and factorial normalization. *)
Theorem analytic_initial_taylor_remainder
    (alpha:analytic_germ_space hNX (0:X)) k (P:X->R)
    (f:@analytic_representative_type R X NX hNX 0):
  is_initial_analytic_germ_polynomial alpha k P ->analytic_germ f=alpha ->
  @is_homogeneous_polynomial R X R^o k P /\
  norm_class_zero NX N setT P /\
  (forall (t:R) v,P (t*:v)=t^+k*P v) /\
  forall e:R,0<e ->exists r:R,0<r /\forall x,NX x<r ->
    `|analytic_representative_value f x-P x|<=e*(NX x)^+k.
Proof.
move=>[hPositive [hTop [hLower hFormula]]] hGerm.
case:k hPositive hTop hLower hFormula=>[|k] // hPositive hTop hLower hFormula.
have [U [c [ha [hUT [hClass hBound]]]]]:=analytic_representative_analytic f.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX N hNX hN U
  (analytic_representative_value f) hClass.
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hClass 0%N).1 x hx).1.
have hJet i:D i 0=@AnalyticGermJets.value R X NX hNX 0 i alpha.
  have hFull:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN
    Z ev ZN hZ i setT U (analytic_representative_value f) hUT hOpen 0 ha (D i 0)).2
    ((hD i).1 0 ha).
  exact:(@norm_higher_differential_unique R X R^o NX N hNX hN Z ev ZN hZ
    setT (analytic_representative_value f) i 0 _ _ hFull
    (@AnalyticGermJets.laws R X NX hNX 0 i alpha f hGerm)).
have hDLower i (hi:(i<k.+1)%N):D i 0=0 by rewrite hJet (hLower i hi).
have hTaylor:=@leading_actual_taylor_remainder R X NX hNX U
  (analytic_representative_value f) D k ha (fun i hi=>(hD i).1) (hD k.+1).2 hDLower.
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
