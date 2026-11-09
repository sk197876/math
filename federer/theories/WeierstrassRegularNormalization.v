(** Federer (1969), 3.4.6, p. 322: normalize
    the original nonzero divided leading coefficient while
    retaining the original direction and transverse functional. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticGermJetsSealed
  WeierstrassRegularUP WeierstrassRegularCoefficients WeierstrassScalarGermArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_regular_normalization]: multiplication
    by the inverse of the actual divided kth coefficient
    gives a regular germ with divided kth coefficient one,
    3.4.6, p. 322. The bound already absorbs
    the original norm of v, so v and every supplied
    xi remain unchanged. No normalization hypothesis is
    retained in the final numbered theorem. *)
Theorem weierstrass_regular_normalization (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) k (v:X)
    (Phi:@analytic_germ_ring R X NX hNX 0):
  is_weierstrass_regular_germ Phi k v ->
  exists c:R,c!=0 /\
    is_weierstrass_regular_germ
      ((analytic_germ (@analytic_constant_representative R X NX hNX 0 c):
        @analytic_germ_ring R X NX hNX 0)*Phi) k v /\
    ((k`!)%:R)^-1*@ContinuousMultilinear.evaluation R k X R^o NX (fun r=>`|r|)
      hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
      (@AnalyticGermJets.value R X NX hNX 0 k
        ((analytic_germ (@analytic_constant_representative R X NX hNX 0 c):
          @analytic_germ_ring R X NX hNX 0)*Phi))= 1.
Proof.
move=>hRegular.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R).
pose jet i:=@AnalyticGermJets.value R X NX hNX 0 i.
pose a:=((k`!)%:R)^-1*ev k [ffun _:'I_k=>v] (jet k Phi).
have hA:a!=0 by apply/eqP;exact:weierstrass_regular_leading_nonzero hRegular.
pose c:=a^-1.
pose gamma:@analytic_germ_ring R X NX hNX 0:=(analytic_germ (@analytic_constant_representative R X NX hNX 0 c):@analytic_germ_ring R X NX hNX 0)*Phi.
have hScale i:ev i [ffun _:'I_i=>v] (jet i gamma)=c*ev i [ffun _:'I_i=>v] (jet i Phi).
  rewrite /gamma /jet weierstrass_scalar_germ_jet.
  have hLinear:=hom_linear (ev i [ffun _:'I_i=>v]) c (jet i Phi) 0.
  by rewrite addr0 linear0 addr0 in hLinear.
have hUnit:((k`!)%:R)^-1*ev k [ffun _:'I_k=>v] (jet k gamma)= 1.
  rewrite hScale.
  have hReorder:((k`!)%:R:R)^-1*(c*ev k [ffun _:'I_k=>v] (jet k Phi))=c*a by rewrite /a;ring.
  by rewrite hReorder /c mulVf.
exists c;split;first by rewrite /c invr_eq0.
split;last exact:hUnit.
split;first exact:hRegular.1.
split.
- move=>i hi;by rewrite hScale (hRegular.2.1 i hi) mulr0.
- move=>hZero.
  have hImpossible:=hUnit;rewrite hZero mulr0 in hImpossible.
  have hNot:(1:R)!=0:=oner_neq0 R.
  by rewrite -hImpossible eqxx in hNot.
Qed.
