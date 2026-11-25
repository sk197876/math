(** Federer (1969), 4.1.17, p. 374: the original flat
    currents with finite mass are exactly the mass closure
    of the supported normal currents. Reuse the preceding
    attained normal filling and original closure predicates.
    The normal approximant is Q+boundary S, as corrected by
    Federer's May 1987 erratum, p. 7, book p. 374 line 16. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentSupportGeometry CurrentMassSealed
  CurrentMassBasic CurrentMassFiniteAlgebra CompactRepresentedCurrentMass
  CurrentBoundary CurrentBoundarySupport NormalCurrentsUP NormalCurrentLinear
  NormalCurrentBoundary CurrentFlatNorm CurrentFlatMinimum FlatCurrentsUP
  FlatCurrentFinite CurrentNormalMassClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatFiniteMassClosure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU K).
Local Notation closureM := (@is_normal_current_mass_closure R h2 n m U hU K).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation boundary := (@current_boundary R h2 n m U hU).

(** Source for [normal_current_mass_closure_finite]: the
    mass closure in Federer 4.1.17, p. 374, has finite
    mass. One original normal approximant at tolerance one
    and the preceding finite-mass linearity suffice. Neither
    support nor finite mass is imposed on the candidate. *)
Theorem normal_current_mass_closure_finite (T:C):
  closureM T->(M T< +oo)%E.
Proof.
move=>hClosure.
have[Q [hQ hError]]:=hClosure 1 ltr01.
have hQFinite:=@compact_represented_current_finite_mass R h2 n m U hU Q
  hQ.1.1.1 hQ.1.2.
have hDifference:(M (T-Q)< +oo)%E:=lt_trans hError (ltry 1).
have h:=@current_finite_mass_linear_combination R h2 n m U hU
  1 (T-Q) Q hDifference hQFinite.
by rewrite scale1r subrK in h.
Qed.

(** Source for [flat_finite_mass_normal_approximation]: the
    printed proof of Federer 4.1.17, p. 374: approximate
    in the flat seminorm, then use its attained normal
    filling to obtain a normal mass approximant in the same
    K. The approximant matching T-Q-boundary S is Q+boundary S,
    as corrected at erratum p. 7, book p. 374 line 16. *)
Theorem flat_finite_mass_normal_approximation (T:C):
  flatK T->(M T< +oo)%E->closureM T.
Proof.
move=>hFlat hMass epsilon hEpsilon.
have hSupport:=@flat_current_supported_support R h2 n m U hU K T hFlat.
have[Q [hQ hError]]:=hFlat epsilon hEpsilon.
have hQFinite:=@compact_represented_current_finite_mass R h2 n m U hU Q
  hQ.1.1.1 hQ.1.2.
have hDifferenceFinite:(M (T-Q)< +oo)%E.
  have h:=@current_finite_mass_linear_combination R h2 n m U hU
    (-1) Q T hQFinite hMass.
  by rewrite scaleN1r addrC in h.
have hDifferenceSupport:support (T-Q) `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K
    (-1) Q T hQ.2 hSupport.
  by rewrite scaleN1r addrC in h.
have[S [hNormalS hMinimum]]:=@current_flat_minimum_normal_filling
  R h2 n m U hU K (T-Q) hDifferenceSupport hDifferenceFinite.
have hBoundaryNormal:=@normal_current_boundary R h2 n U hU m S hNormalS.
have hBoundarySupport:support (boundary S) `<=` smooth_compact_carrier K.
  move=>x hx;apply:hMinimum.1.
  exact:(@current_boundary_support_subset R h2 n m U hU S x hx).
exists (Q+boundary S);split.
- split.
  + have h:=@normal_current_linear R h2 n U hU m 1
      Q (boundary S) hQ.1 hBoundaryNormal.
    by rewrite scale1r in h.
  + have h:=@current_support_linear_subset R h2 n m U hU K
      1 Q (boundary S) hQ.2 hBoundarySupport.
    by rewrite scale1r in h.
- have hResidual:T-(Q+boundary S)=(T-Q)-boundary S.
    by rewrite opprD addrA.
  rewrite hResidual.
  have hBound:=leeDl (M ((T-Q)-boundary S))
    (@current_mass_nonnegative R h2 n m.+1 U hU S).
  rewrite -hMinimum.2.1 in hBound.
  exact:le_lt_trans hBound hError.
Qed.

(** Source for [federer_4_1_17_mass_closure]: the first
    complete assertion of Federer 4.1.17, p. 374:
    F_(m,K) intersect finite mass equals the M closure
    of N_(m,K). Every original candidate current is allowed;
    all original degree and empty-domain cases are retained. *)
Theorem federer_4_1_17_mass_closure (T:C):
  (flatK T /\(M T< +oo)%E)<->closureM T.
Proof.
split.
- move=>[hFlat hMass];exact:flat_finite_mass_normal_approximation hFlat hMass.
- move=>hClosure;split.
  + exact:(@normal_current_mass_closure_is_flat R h2 n m U hU K T hClosure).
  + exact:normal_current_mass_closure_finite hClosure.
Qed.
End FlatFiniteMassClosure.
