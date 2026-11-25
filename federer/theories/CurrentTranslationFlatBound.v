(** Federer (1969), 4.1.18, p. 375: before
    averaging, the original translation difference has
    flat norm at most |z| N(T) on any compact
    containing its support tube. Reuse the original
    homotopy decomposition and sharp fixed-z masses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentBoundarySupport CurrentSupportGeometry
  CurrentMassSealed CurrentMassBasic CurrentNormalMass NormalCurrentsUP
  SmoothCompactSet CurrentFlatNorm CurrentFlatMassComparison CurrentFlatBoundary
  CurrentTranslationChain CurrentTranslationChainMass CurrentTranslationChainHomotopy
  CurrentTranslations CurrentTranslationSupportTube EuclideanClosedSupportTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTranslationFlatBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(fun d=>@current_space R h2 n Full hFull d).
Variable K:smooth_compact_set hNX Full.
Variable r:R.
Variable z:X.
Hypothesis hRadius:NX z<=r.
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d Full hFull).
Local Notation Chain:=(fun d=>@current_translation_chain R h2 n d z).
Local Notation Shift:=(fun d=>@current_translation_pushforward R h2 n d z).
Local Notation F:=(fun d=>@current_flat_norm R h2 n d Full hFull K).

(** Source for [current_translation_positive_flat_finite]:
    the two original fixed-z deformation masses
    bound the positive-degree flat difference,
    by 4.1.13, pp. 369–370, supporting
    4.1.18, p. 375. Both real witnesses
    are the actual masses, not extra bounds. *)
Theorem current_translation_positive_flat_finite j (T:C j.+1) (a b:R):
  M j.+1 T=a%:E ->M j (@current_boundary R h2 n j Full hFull T)=b%:E ->
  @euclidean_closed_support_tube R n
    (@current_support R h2 n Full hFull j.+1 T) r `<=` smooth_compact_carrier K ->
  (F j.+1 ((Shift j.+1 T-T)%R)<=(NX z*(a+b))%R%:E)%E.
Proof.
move=>hMass hBoundaryMass hTube.
pose S:=Chain j.+1 T.
pose B:=@current_boundary R h2 n j Full hFull T.
pose Remainder:=Chain j B.
have hS:@current_support R h2 n Full hFull j.+2 S `<=` smooth_compact_carrier K.
  exact:subset_trans (@current_translation_chain_support_tube R h2 n j.+1 T z r hRadius) hTube.
have hR:@current_support R h2 n Full hFull j.+1 Remainder `<=` smooth_compact_carrier K.
  apply:subset_trans (@current_translation_chain_support_tube R h2 n j B z r hRadius) _.
  apply:subset_trans _ hTube.
  apply:euclidean_closed_support_tube_mono;last exact:lexx.
  exact:current_boundary_support_subset.
have hFormula:=@current_translation_positive_homotopy R h2 n z j T.
have hBoundary:@current_support R h2 n Full hFull j.+1
    (@current_boundary R h2 n j.+1 Full hFull S) `<=` smooth_compact_carrier K.
  exact:subset_trans (@current_boundary_support_subset R h2 n j.+1 Full hFull S) hS.
have hDifference:@current_support R h2 n Full hFull j.+1
    ((Shift j.+1 T-T)%R) `<=` smooth_compact_carrier K.
  rewrite hFormula.
  have h:=@current_support_linear_subset R h2 n j.+1 Full hFull K 1
    (@current_boundary R h2 n j.+1 Full hFull S) Remainder hBoundary hR.
  by rewrite scale1r in h.
have hCost:=@current_flat_decomposition_lower_bound R h2 n j.+1 Full hFull K
  ((Shift j.+1 T-T)%R) S hDifference hS.
have hResidual:((Shift j.+1 T-T)%R)-@current_boundary R h2 n j.+1 Full hFull S=Remainder.
  by rewrite hFormula addrAC subrr add0r.
rewrite hResidual in hCost.
have hSMass:=@current_translation_chain_finite_mass R h2 n j.+1 z T a hMass.
have hRMass:=@current_translation_chain_finite_mass R h2 n j z B b hBoundaryMass.
apply:(le_trans hCost).
have h:=leeD hRMass hSMass.
have hEqual:((NX z*b)%R%:E+(NX z*a)%R%:E)%E=(NX z*(a+b))%R%:E.
  rewrite -EFinD;congr (_%:E);ring.
by rewrite hEqual in h.
Qed.

(** Source for [current_translation_zero_flat_finite]:
    the original zero-degree case has only the
    one deformation mass, with no negative-degree
    boundary, supporting 4.1.18, p. 375. *)
Theorem current_translation_zero_flat_finite (T:C 0%N) (a:R):
  M 0%N T=a%:E ->
  @euclidean_closed_support_tube R n
    (@current_support R h2 n Full hFull 0%N T) r `<=` smooth_compact_carrier K ->
  (F 0%N ((Shift 0%N T-T)%R)<=(NX z*a)%R%:E)%E.
Proof.
move=>hMass hTube.
rewrite current_translation_zero_homotopy.
apply:(le_trans (@current_flat_boundary_bound R h2 n 0%N Full hFull K (Chain 0%N T))).
apply:(le_trans (@current_flat_norm_le_mass R h2 n 1%N Full hFull K (Chain 0%N T) _)).
- exact:subset_trans (@current_translation_chain_support_tube R h2 n 0%N T z r hRadius) hTube.
- exact:current_translation_chain_finite_mass hMass.
Qed.

(** Source for [current_translation_flat_bound]: the
    original fixed-z flat bound is |z| N(T),
    including zero degree and dimension zero.
    Finite N is all that the quantitative
    step needs; no representation witness is
    required from the caller. *)
Theorem current_translation_flat_bound m (T:C m):
  (@current_normal_mass R h2 n Full hFull m T< +oo)%E ->
  @euclidean_closed_support_tube R n
    (@current_support R h2 n Full hFull m T) r `<=` smooth_compact_carrier K ->
  (F m ((Shift m T-T)%R)<=(NX z)%:E*
    @current_normal_mass R h2 n Full hFull m T)%E.
Proof.
case:m T=>[|j] T hFinite hTube.
- have[a [_ hMass]]:=@current_finite_mass_value R h2 n 0%N Full hFull T hFinite.
  rewrite current_normal_mass_zero_degree hMass -EFinM.
  exact:current_translation_zero_flat_finite hMass hTube.
- pose B:=@current_boundary R h2 n j Full hFull T.
  have hMA:=@current_mass_nonnegative R h2 n j.+1 Full hFull T.
  have hMB:=@current_mass_nonnegative R h2 n j Full hFull B.
  have hLeft:(M j.+1 T<=M j.+1 T+M j B)%E.
    rewrite -[leLHS](adde0 (M j.+1 T));exact:leeD2l hMB.
  have hRight:(M j B<=M j.+1 T+M j B)%E.
    rewrite addeC -[leLHS](adde0 (M j B));exact:leeD2l hMA.
  have[a [_ hMass]]:=@current_finite_mass_value R h2 n j.+1 Full hFull T
    (le_lt_trans hLeft hFinite).
  have[b [_ hBoundaryMass]]:=@current_finite_mass_value R h2 n j Full hFull B
    (le_lt_trans hRight hFinite).
  rewrite current_normal_mass_positive_degree hMass hBoundaryMass -EFinD -EFinM.
  exact:current_translation_positive_flat_finite hMass hBoundaryMass hTube.
Qed.
End CurrentTranslationFlatBound.
