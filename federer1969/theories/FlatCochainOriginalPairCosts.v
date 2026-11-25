(** Federer (1969), 4.1.19, p. 377: the
    two preceding quantitative q assertions give the
    actual pair presentation used by flat cochains.
    A requested cost error is independent of the
    radius of a tube contained in the original U. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm CurrentFlatDualSeminormBasic
  FlatCurrentsUP FlatCurrentFinite FlatCurrentUnionSpace
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentLonePairCost
  CurrentLonePairFlatMembership CurrentLonePairFlatSealed CurrentLonePairFlatLaws
  CurrentCompactClosedTubeInside CurrentFlatLonePairRepresentation
  EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OriginalPairCosts.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation Q := (@CurrentLonePairFlat.map R h2 n m U hU).
Local Notation raw := (@CurrentLonePair.map R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).
Local Notation support d :=
  (@compact_summable_multivector_ambient_support R h2 n d U hU).

(** Source for [flat_cochain_original_pair_first_cost]:
    the first cost assertion of 4.1.18, p. 375,
    applies to the actual flat-valued q used in
    Federer 4.1.19, p. 377. Each original
    pair has one compact flat index with F_K(q)<=J;
    no norm on the entire union is introduced. *)
Theorem flat_cochain_original_pair_first_cost (v : P) :
  exists K : smooth_compact_set hNX U,
    flatK K (inc (Q v)) /\ fine (FK K (inc (Q v)))<=J v.
Proof.
pose L := support m v.1 `|` support m.+1 v.2.
pose hLCompact := compactU
  (@compact_summable_multivector_ambient_support_laws R h2 n m U hU v.1).1
  (@compact_summable_multivector_ambient_support_laws R h2 n m.+1 U hU v.2).1.
have hLU : L `<=` U.
  move=> x [hx|hx].
  - exact: (@compact_summable_multivector_ambient_support_laws
      R h2 n m U hU v.1).2.1 x hx.
  - exact: (@compact_summable_multivector_ambient_support_laws
      R h2 n m.+1 U hU v.2).2.1 x hx.
pose C := @Build_smooth_compact_set R X NX hNX U L hLU hLCompact.
have [rho [hRho hInside]] :=
  @current_compact_closed_tube_inside_exists R n U hU C.
pose K := @Build_smooth_compact_set R X NX hNX U
  (@euclidean_closed_support_tube R n L rho) hInside
  (@euclidean_closed_support_tube_norm_compact R n L rho hLCompact).
have [hFlat hBound] :=
  @current_lone_pair_flat_membership R h2 n m U hU v rho hRho hInside.
change (flatK K (raw v)) in hFlat.
change (is_true ((FK K (raw v)<=(J v)%:E)%E)) in hBound.
have hFinite := @flat_current_supported_finite R h2 n m U hU K (raw v) hFlat.
have [a [hA hValue]] := @current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m (raw v)) hFinite.
change (FK K (raw v)=a%:E) in hValue.
rewrite hValue lee_fin in hBound.
exists K; rewrite current_lone_pair_flat_value; split; first exact: hFlat.
by rewrite hValue.
Qed.

(** Source for [flat_cochain_original_pair_second_cost]:
    the arbitrary positive cost error in Federer
    4.1.19, p. 377, follows from the
    exact tube-and-cost representation of 4.1.18,
    pp. 375–376. Choose a radius at most
    the requested error and at most an internally
    derived tube margin. Empty K and U remain. *)
Theorem flat_cochain_original_pair_second_cost
    (K : smooth_compact_set hNX U) (T : W) :
  flatK K (inc T) -> forall delta : R, 0<delta ->
  exists v : P, Q v=T /\ J v<=fine (FK K (inc T))+delta.
Proof.
move=> hFlat delta hDelta.
have [rho [hRho hTube]] :=
  @current_compact_closed_tube_inside_exists R n U hU K.
pose epsilon := Num.min delta rho.
have hEpsilon : 0<epsilon by rewrite /epsilon lt_min hDelta hRho.
have hEpsilonDelta : epsilon<=delta by rewrite /epsilon ge_min lexx.
have hEpsilonRho : epsilon<=rho by rewrite /epsilon ge_min lexx orbT.
have hInside : @euclidean_closed_support_tube R n
    (smooth_compact_carrier K) epsilon `<=` U.
  exact: (subset_trans
    (@euclidean_closed_support_tube_mono R n (smooth_compact_carrier K)
      (smooth_compact_carrier K) epsilon rho (fun _ h => h) hEpsilonRho) hTube).
have [v [hValue [_ [_ hCost]]]] :=
  @current_flat_lone_pair_representation R h2 n m U hU
    K (inc T) epsilon hFlat hEpsilon hInside.
have hQ : Q v=T.
  apply: (@flat_current_union_inclusion_injective R h2 n m U hU).
  by rewrite current_lone_pair_flat_value.
have hFinite := @flat_current_supported_finite R h2 n m U hU K (inc T) hFlat.
have [a [hA hNorm]] := @current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m (inc T)) hFinite.
change (FK K (inc T)=a%:E) in hNorm.
rewrite hNorm -EFinD lee_fin in hCost.
exists v; split; first exact: hQ.
rewrite hNorm; exact: (le_trans hCost (lerD (lexx a) hEpsilonDelta)).
Qed.
End OriginalPairCosts.
