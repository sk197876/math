(** Federer (1969), 3.4.2(6), p. 312: geometry of the segment
    retracted onto the original manifold. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalManifoldChartLaws CriticalCompactTube CriticalTubeLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Segment.
Variable R:realType.
Variables m mu k:nat.
Local Notation X:=(R_n R m).
Local Notation N:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Z:subspace X.
Variable S C T:set X.
Variable p:euclidean_projection_space R m mu.
Variable g:R_n R mu->X.
Hypothesis hChart:is_critical_manifold_chart k Z S p g.
Local Notation P:=(euclidean_projection_linear p).
Local Notation r:=(fun x=>g (P x)).
Local Notation U:=(fun x=>(P @` S) (P x)).
Variables e M:R.
Hypothesis hTube:is_critical_source_tube C e T.
Hypothesis hCS:C `<=` S.
Hypothesis hTU:T `<=` U.
Hypothesis hM:1<=M.
Hypothesis hLip:forall x y,T x ->T y ->N (r x-r y)<=M*N (x-y).

(** Source for [critical_retracted_segment_geometry]: the curve
    g(t)=r(c+t(x-c)) in the proof of 3.4.2(6), p. 312. For positive
    t it stays in S, remains in the same Z fibre, and has positive
    distance at most M delta from c. Projection univalence proves
    that the distance is positive; the original punctured quotient
    therefore applies at every positive parameter. *)
Theorem critical_retracted_segment_geometry x c delta t:
  S x ->C c ->Z (x-c) ->0<N (x-c)<=delta ->delta<e ->0<t<=1 ->
  norm_domain_interior N T (c+t*:(x-c)) /\
  S (r (c+t*:(x-c))) /\Z (r (c+t*:(x-c))-c) /\
  0<N (r (c+t*:(x-c))-c)<=M*delta /\
  N (r (c+t*:(x-c))-c)<=M*N (x-c).
Proof.
move=>hx hc hZ hDist hDelta hTime.
pose a:=c+t*:(x-c).
have [ht0 ht1]:=andP hTime.
have hw0:0<=N (x-c):=inner_norm_nonnegative _ _.
have hSegment:a-c=t*:(x-c) by rewrite /a addrAC subrr add0r.
have hNorm:N (a-c)=t*N (x-c).
  by rewrite hSegment inner_normZ (ger0_norm (ltW (andP hTime).1)).
have hSmall:N (a-c)<e.
  have hBound:t*N (x-c)<=N (x-c).
    nra.
  rewrite hNorm;exact:(le_lt_trans (le_trans hBound (andP hDist).2) hDelta).
have hInterior:=critical_source_tube_interior hTube hc hSmall.
have haT:T a:=norm_domain_interior_member hN hInterior.
have haU:U a:=hTU haT.
have he:0<=e:=ltW (lt_trans (lt_le_trans (andP hDist).1 (andP hDist).2) hDelta).
have hcT:T c:=@critical_source_tube_contains_source R m C T e hTube he c hc.
have hcS:S c:=hCS hc.
have hRc:r c=c:=critical_chart_left_inverse hChart hcS.
have [haS haZ]:=critical_chart_retraction_displacement hChart haU.
have hZac:Z (a-c) by rewrite hSegment;exact:subspace_scale.
have hZbc:Z (r a-c).
  have hh:=subspace_add haZ hZac.
  by rewrite addrA subrK in hh.
have hLipBound:=@hLip a c haT hcT.
rewrite hRc in hLipBound.
have hDistance:N (r a-c)<=M*N (x-c).
  apply:(le_trans hLipBound).
  have hM0:0<=M:=le_trans ler01 hM.
  rewrite hNorm.
  have hBound:t*N (x-c)<=N (x-c).
    nra.
  exact:(ler_wpM2l hM0 hBound).
have hNotEqual:r a!=c.
  apply/eqP=>hEqual.
  have hProjection:P a= P c.
    have hh: P (r a)= P a:=(critical_chart_right_inverse hChart haU).2.
    by rewrite hEqual in hh.
  have hZero:t*:P (x-c)=0.
    have hh:=congr1 (fun v=>v-P c) hProjection.
    by rewrite /a linearD linearZ addrAC !subrr add0r in hh.
  have ht:t!=0 by rewrite gt_eqF.
  have hKernel:P (x-c)=0.
    apply:(scalerI ht);by rewrite hZero scaler0.
  have hEqP:P x= P c by apply/eqP;rewrite -subr_eq0 -linearB hKernel.
  have hEq:=critical_chart_projection_injective hChart hx hcS hEqP.
  have hh:0<N (x-c):=(andP hDist).1.
  by rewrite hEq subrr inner_norm0 ltxx in hh.
have hPositive:0<N (r a-c) by rewrite inner_norm_gt0 subr_eq0.
split;first exact:hInterior.
split;first exact:haS.
split;first exact:hZbc.
split;last exact:hDistance.
apply/andP;split;first exact:hPositive.
apply:(le_trans hDistance).
exact:(ler_wpM2l (le_trans ler01 hM) (andP hDist).2).
Qed.
End Segment.
