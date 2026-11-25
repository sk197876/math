(** Federer (1969), 4.1.18, p. 375: two
    L1-approximated finite-mass density pieces give a
    flat current A+boundary B on the same compact
    support allowance. The boundary may have infinite
    mass; no mass premise on A+boundary B is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentBoundarySupport CurrentSupportGeometry
  CurrentMassSealed CurrentFlatNorm CurrentFlatMassComparison FlatCurrentsUP
  NormalCurrentsUP NormalCurrentLinear NormalCurrentBoundary SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PairFlatApproximation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable K:smooth_compact_set hNX U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation support:=(@current_support R h2 n U hU m).
Local Notation supportNext:=(@current_support R h2 n U hU m.+1).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation NextM:=(@CurrentMass.value R h2 n m.+1 U hU).

(** Source for [current_finite_mass_pair_flat_approximation]:
    the two ordinary field L1 limits prove
    the first proposition's normal-closure membership,
    Federer 4.1.18, p. 375. This internal
    adapter uses the original normal approximants and
    the preceding exact mass-decomposition inequality. *)
Theorem current_finite_mass_pair_flat_approximation (A:C) (B:Next)
    (P:R->C) (Q:R->Next) (r:R):
  support A `<=` smooth_compact_carrier K ->
  supportNext B `<=` smooth_compact_carrier K ->
  0<r ->
  (forall epsilon,0<epsilon->epsilon<r->
    @normal_currents_supported_in R h2 n U hU m K (P epsilon) /\
    @normal_currents_supported_in R h2 n U hU m.+1 K (Q epsilon)) ->
  (forall eta,0<eta->exists d:R,0<d /\forall epsilon,0<epsilon->epsilon<d->
    (M (A-P epsilon)+NextM (B-Q epsilon)<eta%:E)%E) ->
  @is_flat_current_supported_in R h2 n m U hU K (A+bd B).
Proof.
move=>hA hB hR hNormal hLimit eta hEta.
have[d [hD hSmall]]:=@hLimit eta hEta.
pose epsilon:=Num.min r d/2.
have hMin:0<Num.min r d by rewrite lt_min hR hD.
have hEpsilon:0<epsilon by rewrite /epsilon divr_gt0 // ltr0n.
have hBelow:epsilon<Num.min r d by rewrite /epsilon;lra.
have /andP [hER hED]:(epsilon<r)&&(epsilon<d) by rewrite -lt_min.
have[hP hQ]:=@hNormal epsilon hEpsilon hER.
pose S:=P epsilon+bd (Q epsilon).
have hBoundarySupport:support (bd (Q epsilon)) `<=` smooth_compact_carrier K.
  move=>x hx;apply:hQ.2.
  exact:(@current_boundary_support_subset R h2 n m U hU (Q epsilon) x hx).
have hSNormal:@is_normal_current R h2 n U hU m S.
  have h:=@normal_current_linear R h2 n U hU m 1 (P epsilon) (bd (Q epsilon))
    hP.1 (@normal_current_boundary R h2 n U hU m (Q epsilon) hQ.1).
  by rewrite scale1r in h.
have hSSupport:support S `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K 1
    (P epsilon) (bd (Q epsilon)) hP.2 hBoundarySupport.
  by rewrite scale1r in h.
have hADifference:support (A-P epsilon) `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K (-1) (P epsilon) A hP.2 hA.
  by rewrite scaleN1r addrC in h.
have hBDifference:supportNext (B-Q epsilon) `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m.+1 U hU K (-1) (Q epsilon) B hQ.2 hB.
  by rewrite scaleN1r addrC in h.
have hBoundaryDifference:support (bd (B-Q epsilon)) `<=` smooth_compact_carrier K.
  move=>x hx;apply:hBDifference.
  exact:(@current_boundary_support_subset R h2 n m U hU (B-Q epsilon) x hx).
have hError:(A+bd B)-S=(A-P epsilon)+bd (B-Q epsilon).
  by rewrite /S opprD addrACA linearB.
have hErrorSupport:support ((A+bd B)-S) `<=` smooth_compact_carrier K.
  rewrite hError.
  have h:=@current_support_linear_subset R h2 n m U hU K 1
    (A-P epsilon) (bd (B-Q epsilon)) hADifference hBoundaryDifference.
  by rewrite scale1r in h.
have hBound:=@current_flat_decomposition_lower_bound R h2 n m U hU K
  ((A+bd B)-S) (B-Q epsilon) hErrorSupport hBDifference.
rewrite hError addrK in hBound.
exists S;split;first exact:conj hSNormal hSSupport.
rewrite hError.
exact:(le_lt_trans hBound (@hSmall epsilon hEpsilon hED)).
Qed.
End PairFlatApproximation.
