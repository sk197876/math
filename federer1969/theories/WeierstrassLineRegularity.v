(** Federer (1969), 3.4.6, pp. 321–322: an
    exact original line value a*t^k with a nonzero
    proves the required actual directional regularity. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormRegularity NormHigherDifferentialUP NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal
  AnalyticGermNeighbourhood AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsSealed
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine WeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_line_regularity]: the actual
    derivatives of an original analytic representative have
    order k in direction v when its line restriction
    is a nonzero scalar multiple of t^k, testing
    exactly the hypotheses of 3.4.6, pp. 321–322.
    Taylor coefficient uniqueness proves every regularity premise. *)
Theorem weierstrass_line_regularity (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (f:analytic_representative_type hNX (0:X))
    k (v:X) (a:R):
  (0<k)%N ->a!=0 ->(forall t:R,analytic_representative_value f (t*:v)=a*t^+k) ->
  is_weierstrass_regular_germ (analytic_germ f) k v.
Proof.
move=>hK hA hLine.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
pose F:=analytic_representative_value f.
pose alpha:=analytic_germ f.
have [U [ha [_ [_ hf]]]]:=@analytic_germ_open_representative R X R^o NX N hNX hN
  setT F 0 (analytic_representative_analytic f).
have hOpen x (hx:U x):norm_domain_interior NX U x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have hDirectional i:((i`!)%:R)^-1*ev i [ffun _:'I_i=>v]
    (@AnalyticGermJets.value R X NX hNX 0 i alpha)=if (i==k)%N then a else 0.
  have [c [hc _]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN U F i v hf.
  have hExact t (ht:`|t|<1):F (0+t*:v)=
      \sum_(n<k.+1) t^+n*(if ((n:nat)==k)%N then a else 0).
    rewrite add0r /F hLine (bigD1 (Ordinal (ltnSn k))) //= eqxx.
    have hOthers:(\sum_(n<k.+1 | n!=Ordinal (ltnSn k))
      t^+n*(if ((n:nat)==k)%N then a else 0))=0.
      apply:big1=>n hn.
      have hNe:((n:nat)!=k)%N by move:hn;rewrite -val_eqE /=.
      by rewrite (negbTE hNe) mulr0.
    by rewrite hOthers addr0 mulrC.
  have hFinite:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN
    U F i v 0 c k.+1 (fun n=>if (n==k)%N then a else 0) 1 ha hf hc ltr01 hExact.
  have hJet:=@AnalyticGermJets.laws R X NX hNX 0 i alpha f (erefl _).
  have hLocal:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
    i setT U F (fun x _=>Logic.I) hOpen 0 ha (@AnalyticGermJets.value R X NX hNX 0 i alpha)).1 hJet.
  have hAt:=hc 0 ha (@AnalyticGermJets.value R X NX hNX 0 i alpha) hLocal.
  change (c 0=((i`!)%:R)^-1*ev i [ffun _:'I_i=>v] (@AnalyticGermJets.value R X NX hNX 0 i alpha)) in hAt.
  rewrite -hAt hFinite.
  case hSmall:(i<k.+1)%N=>//.
  have hNe:(i!=k)%N by apply/eqP=>h;by rewrite h ltnSn in hSmall.
  by rewrite (negbTE hNe).
split;first exact:hK.
split.
- move=>i hi.
  have hNe:(i!=k)%N by apply/eqP=>h;by rewrite h ltnn in hi.
  have hValue:=hDirectional i;rewrite (negbTE hNe) in hValue.
  have hFact:((i`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
  apply/eqP;move/eqP:hValue;by rewrite mulf_eq0 invr_eq0 (negbTE hFact) orFb.
- move=>hZero.
  have hValue:=hDirectional k;rewrite hZero mulr0 eqxx in hValue.
  by rewrite -hValue eqxx in hA.
Qed.
