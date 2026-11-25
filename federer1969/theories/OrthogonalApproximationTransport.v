(** Federer (1969), 4.1.23, p. 379:
    transport an actual rotated polyhedral approximant
    back to the original compact index. Use
    the original sharp smooth flat and mass
    estimates and affine generator-hull transport;
    neither compact index is assumed convex. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient Hom AffineMaps RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth OrthogonalMaps
  CurrentSpaces CurrentSupportGeometry CurrentMassSealed CurrentMassBasic CurrentFlatNorm
  CurrentCompactPushforwardAlgebra SmoothCompactSet PolyhedralCurrentAlgebra PolyhedralNormal
  PolyhedralAffinePushforward OrthogonalSmoothCurrentBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OrthogonalApproximationTransport.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation Compact := (fun T : Current => @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull m T)).
Variable g : {linear X->X}.
Hypothesis hOrthogonal : is_orthogonal_map
  (@euclidean_inner_product R n) (@euclidean_inner_product R n) g.
Local Notation image := (fun (x : X) (_ : True) => Logic.I).
Local Notation hf := (@euclidean_affine_map_smooth R n n Full hFull g (linear_affine_map g)).
Local Notation Push := (fun (P : Current) (hP : Compact P) =>
  @current_compact_map_pushforward R h2 n n Full Full
    hFull hFull g image hf m P hP).
Variables K E : smooth_compact_set hNX Full.
Hypothesis hIndex : forall x, smooth_compact_carrier K x -> smooth_compact_carrier E (g x).
Variables S T : Current.
Hypothesis hCompactS : Compact S.
Hypothesis hSupportS : @current_support R h2 n Full hFull m S `<=` smooth_compact_carrier K.
Hypothesis hFiniteS : (M S< +oo)%E.
Hypothesis hRecovery : Push S hCompactS=T.
Hypothesis hMassCompare : (M S<=M T)%E.

(** Source for [orthogonal_polyhedral_approximation_transport]:
    the inverse rotation sends the
    actual rotated approximant to an
    approximant with the same error
    budget in the original compact,
    supporting Federer 4.1.23, p. 379.
    Recovery and the mass comparison
    are explicit supporting premises, proved
    internally for the original rotated cell. *)
Theorem orthogonal_polyhedral_approximation_transport epsilon
    (P : Current)
    (hPoly : @polyhedral_current_subspace R h2 n m Full hFull K P)
    (hError : (@current_flat_norm R h2 n m Full hFull K (S-P)<=epsilon%:E)%E)
    (hMass : (M P<=M S+epsilon%:E)%E) :
  exists Q : Current, @polyhedral_current_subspace R h2 n m Full hFull E Q /\
    (@current_flat_norm R h2 n m Full hFull E (T-Q)<=epsilon%:E)%E /\
    (M Q<=M T+epsilon%:E)%E.
Proof.
have hNormalP := @real_polyhedral_current_normal_support R h2 n m Full hFull K P hPoly.
pose hCompactP := @current_support_compact_bound R h2 n m Full hFull K P hNormalP.2.
have hSupportDifference : @current_support R h2 n Full hFull m (S-P)
    `<=` smooth_compact_carrier K.
  have h := @current_support_linear_subset R h2 n m Full hFull K
    (-1) P S hNormalP.2 hSupportS.
  by rewrite scaleN1r addrC in h.
pose hCompactDifference := @current_support_compact_bound R h2 n m Full hFull K
  (S-P) hSupportDifference.
have hFiniteError : (@current_flat_norm R h2 n m Full hFull K (S-P)< +oo)%E.
  exact: le_lt_trans hError (ltry epsilon).
have hFlat := @orthogonal_compact_current_flat_bound R h2 n m g hOrthogonal K E hIndex
  (S-P) hCompactDifference hSupportDifference hFiniteError.
pose Q := Push P hCompactP.
have hDifference := @current_compact_map_pushforward_subtract R h2 n n Full Full
  hFull hFull g image hf m S P hCompactS hCompactP hCompactDifference.
rewrite hRecovery -/Q in hDifference.
rewrite hDifference in hFlat.
have [s [_ hS]] := @current_finite_mass_value R h2 n m Full hFull S hFiniteS.
have hFiniteP : (M P< +oo)%E.
  have h := hMass; rewrite hS -EFinD in h.
  exact: le_lt_trans h (ltry (s+epsilon)).
have hMassQ := @orthogonal_compact_current_mass_bound R h2 n m g hOrthogonal
  P hCompactP hFiniteP.
have hPolyQ : @polyhedral_current_subspace R h2 n m Full hFull E Q.
  exact: (@real_polyhedral_current_affine_pushforward R h2 n n m Full Full
    hFull hFull g (linear_affine_map g) image K E hIndex P hPoly hCompactP).
exists Q; split; first exact: hPolyQ.
split; first exact: le_trans hFlat hError.
exact: le_trans (le_trans hMassQ hMass) (leeD hMassCompare (lexx epsilon%:E)).
Qed.
End OrthogonalApproximationTransport.
