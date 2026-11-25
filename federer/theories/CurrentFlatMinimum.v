(** Federer (1969), 4.1.12, pp. 367–368: the
    original flat seminorm is an attained mass
    minimum over fillings supported in K. Retain
    infinite flat values and the original finite-mass
    parenthesis concerning a normal minimising filling. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet CurrentFlatNorm CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic
  CurrentFlatHahnBanachDecomposition CurrentFlatMassComparison CurrentMassSealed
  CurrentMassBasic CurrentMassFiniteAlgebra CurrentFiniteMassRepresentation
  CurrentBoundary CurrentSupportGeometry NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatMinimum.
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
Local Notation NC := (@current_space R h2 n U hU m.+1).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation NextM := (@CurrentMass.value R h2 n m.+1 U hU).
Local Notation boundary := (@current_boundary R h2 n m U hU).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation nextSupport := (@current_support R h2 n U hU m.+1).
Local Notation carrier := (smooth_compact_carrier K).

(** Source for [is_current_flat_minimiser]: the original
    support constraint, exact value and minimum property
    in Federer 4.1.12, pp. 367–368. This
    predicate specifies a minimising filling independently
    of any construction or selection of a witness. *)
Definition is_current_flat_minimiser (T:C) (S:NC):Prop:=
  nextSupport S `<=` carrier /\
  F T=(M ((T-boundary S)%R)+NextM S)%E /\
  forall B:NC,nextSupport B `<=` carrier->
    (M ((T-boundary S)%R)+NextM S<=M ((T-boundary B)%R)+NextM B)%E.

(** Source for [current_flat_minimum_attained]: for every
    original current supported in K, F_K(T) is the
    minimum of M(T-boundary S)+M(S) over S supported
    in K, Federer 4.1.12, pp. 367–368.
    The statement includes F_K(T)=infinity. *)
Theorem current_flat_minimum_attained (T:C):
  support T `<=` carrier->exists S:NC,is_current_flat_minimiser T S.
Proof.
move=>hSupport.
case:(ltP (F T) (+oo)%E)=>hFinite.
- have [c [hc hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K (action T) hFinite.
  have hFlat:F T=c%:E:=hValue.
  have [A [S [hDecomposition [hA [hS hCost]]]]]:=
    @current_flat_hahn_banach_decomposition R h2 n m U hU K T c hValue.
  have hResidual:T-boundary S=A by rewrite hDecomposition addrK.
  have hEquality:F T=(M ((T-boundary S)%R)+NextM S)%E.
    apply/eqP;rewrite eq_le;apply/andP;split.
    + exact:(@current_flat_decomposition_lower_bound R h2 n m U hU K T S hSupport hS).
    + by rewrite hResidual hFlat.
  exists S;split;first exact:hS.
  split;first exact:hEquality.
  move=>B hB;rewrite -hEquality.
  exact:(@current_flat_decomposition_lower_bound R h2 n m U hU K T B hSupport hB).
- have hZeroSupport:=@current_support_zero_subset R h2 n m.+1 U hU K.
  have hEquality:F T=(M ((T-boundary (0:NC))%R)+NextM (0:NC))%E.
    rewrite (linear0 boundary) subr0 current_mass_zero adde0.
    apply/eqP;rewrite eq_le;apply/andP;split.
    + exact:(@current_flat_norm_le_mass R h2 n m U hU K T hSupport).
    + exact:le_trans (leey (M T)) hFinite.
  exists (0:NC);split;first exact:hZeroSupport.
  split;first exact:hEquality.
  move=>B hB;rewrite -hEquality.
  exact:(@current_flat_decomposition_lower_bound R h2 n m U hU K T B hSupport hB).
Qed.

(** Source for [current_flat_minimum_normal_filling]: if
    the original T has finite mass, a minimising S
    can be chosen normal, the parenthetical assertion
    of Federer 4.1.12, pp. 367–368. Both
    masses and compact support required for normality
    are proved, without changing the minimum problem. *)
Theorem current_flat_minimum_normal_filling (T:C):
  support T `<=` carrier->(M T < +oo)%E->
  exists S:NC,@is_normal_current R h2 n U hU m.+1 S /\is_current_flat_minimiser T S.
Proof.
move=>hSupport hMass.
have [S hMinimum]:=current_flat_minimum_attained hSupport.
have [hS [hEquality hLeast]]:=hMinimum.
have hFlat:(F T < +oo)%E.
  exact:le_lt_trans (@current_flat_norm_le_mass R h2 n m U hU K T hSupport) hMass.
have hCost:(M ((T-boundary S)%R)+NextM S < +oo)%E by rewrite -hEquality.
have hSFinite:(NextM S < +oo)%E.
  exact:le_lt_trans (leeDr (NextM S)
    (@current_mass_nonnegative R h2 n m U hU (T-boundary S))) hCost.
have hResidualFinite:(M ((T-boundary S)%R) < +oo)%E.
  exact:le_lt_trans (leeDl (M (T-boundary S))
    (@current_mass_nonnegative R h2 n m.+1 U hU S)) hCost.
have hBoundaryFinite:(M (boundary S) < +oo)%E.
  have h:=@current_finite_mass_linear_combination R h2 n m U hU (-1)
    (T-boundary S) T hResidualFinite hMass.
  by rewrite scaleN1r addrC subKr in h.
exists S;split;last exact:hMinimum.
split.
- split.
  + exact:(@current_finite_mass_representation R h2 n m.+1 U hU S hSFinite).
  + exact:(@current_finite_mass_representation R h2 n m U hU (boundary S) hBoundaryFinite).
- exact:(@current_support_compact_bound R h2 n m.+1 U hU K S hS).
Qed.
End CurrentFlatMinimum.
