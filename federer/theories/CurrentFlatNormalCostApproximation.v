(** Federer (1969), 4.1.18, p. 376: choose supported
    normal R_i and S_i with small flat residual and nearly
    least mass cost. The normal approximation from 4.1.12,
    p. 368, is followed by its attained normal filling.
    Finite mass is needed only for the chosen normal approximant;
    the original flat current may have infinite mass. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentSupportGeometry CurrentMassSealed
  CompactRepresentedCurrentMass CurrentBoundary CurrentBoundarySupport
  NormalCurrentsUP NormalCurrentBoundary NormalCurrentLinear
  CurrentFlatNorm CurrentFlatDualSeminormBasic CurrentFlatMinimum
  CurrentFlatFiniteArithmetic FlatCurrentsUP FlatCurrentFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatNormalCostApproximation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation NextM:=(@CurrentMass.value R h2 n m.+1 U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation normalK:=(@normal_currents_supported_in R h2 n U hU m K).
Local Notation normalNextK:=(@normal_currents_supported_in R h2 n U hU m.+1 K).

(** Source for [current_flat_normal_cost_approximation]:
    the two independent tolerances in the first induction
    display of Federer 4.1.18, p. 376. The actual normal
    currents retain the original K, and the residual has
    arbitrarily small F_K while the mass cost approaches F_K(T).
    No finite mass, representation or normality of T is assumed. *)
Theorem current_flat_normal_cost_approximation (T:C):
  @is_flat_current_supported_in R h2 n m U hU K T->
  forall epsilon delta:R,0<epsilon->0<delta->
  exists A:C,exists S:Next,normalK A /\normalNextK S /\
    (F (T-A-bd S)<epsilon%:E)%E /\
    (M A+NextM S<F T+delta%:E)%E.
Proof.
move=>hFlat epsilon delta hEpsilon hDelta.
have hTolerance:0<Num.min epsilon delta.
  by rewrite lt_min hEpsilon hDelta.
have[Q [hQ hError]]:=hFlat (Num.min epsilon delta) hTolerance.
have hEpsBound:Num.min epsilon delta<=epsilon by rewrite ge_min lexx.
have hDeltaBound:Num.min epsilon delta<=delta by rewrite ge_min lexx orbT.
have hErrorEps:(F (T-Q)<epsilon%:E)%E.
  apply:(lt_le_trans hError);by rewrite lee_fin.
have hErrorDelta:(F (T-Q)<delta%:E)%E.
  apply:(lt_le_trans hError);by rewrite lee_fin.
have hTFinite:=@flat_current_supported_finite R h2 n m U hU K T hFlat.
pose D:C:=T-Q.
have hDFinite:(F D< +oo)%E:=lt_trans hError (ltry _).
have hNeg:=@current_flat_finite_negate R h2 n m U hU K D hDFinite.
have hNegFinite:(F (-D)< +oo)%E by rewrite hNeg.
have hTriangle:=@current_flat_finite_triangle R h2 n m U hU K
  T (-D) hTFinite hNegFinite.
have hIdentity:T+(-D)=Q by rewrite /D opprB addrC subrK.
rewrite hIdentity hNeg in hTriangle.
have[c [hc hC]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m T) hTFinite.
have[d [hd hD]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m D) hDFinite.
change (F T=c%:E) in hC.
change (F D=d%:E) in hD.
have hCost:(F Q<F T+delta%:E)%E.
  apply:(le_lt_trans hTriangle).
  rewrite hC hD -!EFinD lte_fin ltrD2l.
  by move:hErrorDelta;rewrite hD lte_fin.
have hQMass:=@compact_represented_current_finite_mass R h2 n m U hU Q
  hQ.1.1.1 hQ.1.2.
have[S [hNormalS hMinimum]]:=@current_flat_minimum_normal_filling
  R h2 n m U hU K Q hQ.2 hQMass.
have hBoundaryNormal:=@normal_current_boundary R h2 n U hU m S hNormalS.
have hBoundarySupport:
    @current_support R h2 n U hU m (bd S) `<=` smooth_compact_carrier K.
  move=>x hx;apply:hMinimum.1.
  exact:(@current_boundary_support_subset R h2 n m U hU S x hx).
pose A:C:=Q-bd S.
have hANormal:@is_normal_current R h2 n U hU m A.
  have h:=@normal_current_linear R h2 n U hU m (-1)
    (bd S) Q hBoundaryNormal hQ.1.
  by rewrite scaleN1r addrC in h.
have hASupport:
    @current_support R h2 n U hU m A `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K (-1)
    (bd S) Q hBoundarySupport hQ.2.
  by rewrite scaleN1r addrC in h.
have hDecomposition:A+bd S=Q by rewrite /A subrK.
have hResidual:T-A-bd S=T-Q.
  by rewrite -addrA -opprD hDecomposition.
exists A,S;split.
- split;[exact:hANormal|exact:hASupport].
split.
- split;[exact:hNormalS|exact:hMinimum.1].
split;first by rewrite hResidual.
change (M (Q-bd S)+NextM S<F T+delta%:E)%E.
by rewrite -hMinimum.2.1.
Qed.
End CurrentFlatNormalCostApproximation.
