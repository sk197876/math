(** Federer (1969), 3.4.8(11), p. 333:
    each directional witness is nonzero at
    small nonzero points of its coordinate
    axis. Reuse the linewise Taylor remainder
    of 3.1.11 and the actual regular
    germ jets from 3.4.6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialLocal NormHigherDifferentialUnique NormSmoothFields NormTaylorRemainderBound
  NormTaylorLineValues NormTaylorLineRemainder NormLittleOPower NormAnalyticUP NormAnalyticLocal
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsSealed AnalyticGermNeighbourhood
  WeierstrassRegularUP WeierstrassRegularCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_regular_line_isolated_zero]:
    the actual regular representative is nonzero
    along small punctured axis segments,
    3.4.8(11), p. 333. The original
    positive order and arbitrary direction remain;
    no completeness premise is needed. *)
Theorem analytic_regular_line_isolated_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (f:@analytic_representative_type R X NX hNX 0) k v:
  is_weierstrass_regular_germ (analytic_germ f) k v ->
  exists d:R,0<d /\ forall t,0<`|t|<d ->analytic_representative_value f (t*:v)<>0.
Proof.
move=>hRegular.
pose NR:=fun z:R^o=>`|z|;pose hNR:=@scalar_absolute_value_norm R.
pose F:=analytic_representative_value f.
pose alpha:=analytic_germ f.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NR hNX hNR.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NR hNX hNR.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX NR hNX hNR.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX NR hNX hNR.
have [U [hU0 [hUT [hU hAnalytic]]]]:=@analytic_germ_open_representative R X R^o NX NR hNX hNR
  setT F 0 (analytic_representative_analytic f).
have hSmooth:=norm_analytic_class_all_orders hAnalytic.
have hContinuous:=norm_class_continuous (hSmooth 0%N).
have hInterior x (hx:U x):norm_domain_interior NX U x:=(@hContinuous x hx).1.
have [D hD]:=@norm_smooth_fields_exist R X R^o NX NR hNX hNR U F hSmooth.
have hJet i:D i 0 = @AnalyticGermJets.value R X NX hNX 0 i alpha.
  have hActual:=@AnalyticGermJets.laws R X NX hNX 0 i alpha f (erefl _).
  have hRestricted:=(@norm_higher_differential_open_restriction R X R^o NX NR hNX hNR
    Z ev NZ hZ i setT U F hUT hInterior 0 hU0 _).1 hActual.
  exact:(@norm_higher_differential_unique R X R^o NX NR hNX hNR Z ev NZ hZ U F i 0 _ _
    ((hD i).1 0 hU0) hRestricted).
pose c:=((k`!)%:R)^-1*ev k [ffun _:'I_k=>v] (D k 0).
have hC:c<>0.
  rewrite /c hJet;exact:(@weierstrass_regular_leading_nonzero R X NX hNX alpha k v hRegular).
have hTaylor t:@norm_taylor_value R X R^o Z ev D 0 (t*:v) k = t^+k*c.
  rewrite (@norm_taylor_value_on_line R X R^o NX NR Z ev NZ hZ D 0 v t k).
  rewrite (bigD1 (ord_max:'I_k.+1)) //=.
  have hOthers:(\sum_(i<k.+1 | i!=ord_max)
    t^+(i:nat)*:(((i`!)%:R)^-1*:ev i [ffun _:'I_i=>v] (D i 0))) = 0.
    apply:big1=>i hDifferent.
    have hLess:(i<k)%N.
      have hLe:(i<=k)%N:=ltn_ord i.
      rewrite ltn_neqAle hLe andbT;move:hDifferent;by rewrite -val_eqE /=.
    rewrite hJet (hRegular.2.1 i hLess) scaler0 scaler0.
    reflexivity.
  by rewrite hOthers addr0 /c.
have hRemainder:=@norm_taylor_line_little_o_fields R X R^o NX NR hNX hNR Z ev NZ hZ U F D k 0 v
  hU0 hContinuous (fun i _ x hx=>(hD i).1 x hx) (hD k).2.
have hAbs:0<`|c| by rewrite normr_gt0;apply/eqP;exact:hC.
have hHalf:0<`|c|/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hBound]]:=hRemainder (`|c|/2) hHalf.
exists d;split;first exact:hd.
move=>t ht hZero.
have h:=hBound t ht.
rewrite add0r hTaylor /F /NR hZero sub0r normrN normrM normrX in h.
have hPower:0<`|t|^+k:=exprn_gt0 k (andP ht).1.
nra.
Qed.
