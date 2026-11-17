(** Federer (1969), 3.4.8(8), p. 329:
    the original positive directional test gives
    a first nonzero directional order along
    that same direction. This connects B_j
    to the existing preparation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed AnalyticReductionLociUP WeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_directional_regular_order_exists]:
    choose the original r(j) in the
    preparation step of 3.4.8(8), p. 329.
    The direction is the prescribed coordinate
    direction, and the zeroth derivative vanishes.
    The least nonzero directional order meets
    exactly the hypotheses of 3.4.6(2). *)
Theorem analytic_directional_regular_order_exists (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X)) (v:X):
  @AnalyticGermJets.value R X NX hNX 0 0%N alpha = 0 ->
  has_nonzero_analytic_directional_jet alpha v ->
  exists k,is_weierstrass_regular_germ alpha k v.
Proof.
move=>hZeroth [j [hPositive hJ]].
pose value k:=@ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|) hNX
  (@scalar_absolute_value_norm R) [ffun _:'I_k=>v] (@AnalyticGermJets.value R X NX hNX 0 k alpha).
have hExists:exists k,value k!=0 by exists j;apply/eqP;exact:hJ.
have [k hK hMinimal]:=ex_minnP hExists.
have hKPositive:(0<k)%N.
  case:k hK hMinimal=>[|k] hK hMinimal;last exact:ltn0Sn.
  by rewrite /value hZeroth linear0 eqxx in hK.
exists k;split;first exact:hKPositive.
split;last by apply/eqP;exact:hK.
move=>i hi;case:(eqVneq (value i) 0)=>[hZero|hNonzero];first exact:hZero.
have hKI:=hMinimal i hNonzero.
have hFalse:=leq_ltn_trans hKI hi;by rewrite ltnn in hFalse.
Qed.
