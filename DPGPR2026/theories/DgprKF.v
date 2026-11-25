(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:BF (the set K_F, the condition (AC1), the numbers λ(F) and Λ(F))
    and lem:KF.

    For an integrand F of class 1 relative to G(n, k) (Federer 3.1.22)
    the set K_F = conv B_F[G(n, k)] of linear maps of R^n is the convex
    hull of Federer 2.10.2(1), p. 171 ([convex_hull]). The condition
    (AC1) is dim im A ≥ k for A ∈ K_F, expressed by Federer's
    [linear_rank_at_least] (3.1.18). The numbers
    λ(F) = inf { sv_k(A) : A ∈ K_F } and Λ(F) = sup { |A| : A ∈ K_F }
    are characterised by the predicates [is_dgpr_lambda] and
    [is_dgpr_Lambda], which express that they are the greatest lower
    bound and the least upper bound; they are unique
    ([dgpr_lambda_unique], [dgpr_Lambda_unique]) and, under (AC1), exist
    with 0 < λ(F) ≤ Λ(F) ([dgpr_lemma_KF]). No object is chosen. Here
    sv_k is the number of blueprint def:sv ([dgpr_sv]) and |A| the norm
    of Federer 1.7.9. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology normedtype derive.
From Federer Require Import InnerProductUP InnerNorm LinearBasis Hom HomInner OperatorNorm
  HomOperatorNorm GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  HilbertFormCompactness RealNormUP NormMetric NormMetricContinuity RealMetricBackground
  NormClassOneUP RelativeClassUP ConvexHull InnerConvex LinearRankAtLeast HomSpaceNormTopology.
From Allard Require Import AllardGrassmann AllardSetVarifold.
From DPDRG Require Import DdgAnisotropicIntegrand.
From DPGPR Require Import DgprSingularValue DgprSingularValueRank DgprConvexHull
  DgprAnisotropicIntegrand.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section KF.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hH := (hom_inner_productP hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm hH).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation G := (orthogonal_projectors R n k).
Local Notation GA := (projection_grassmann R n k).
Local Notation sv := (dgpr_sv hBn hBn hbn hk).

(** Source for [dgpr_KF]: blueprint def:BF, K_F = conv B_F[G(n, k)],
    with the convex hull of Federer 2.10.2(1), p. 171. Definition. *)
Definition dgpr_KF (F : Hom Rn Rn -> R) : set (Hom Rn Rn) := convex_hull (dgpr_B k F @` G).

(** Source for [dgpr_AC1]: blueprint def:BF and DPGPR 2026, section
    1.2: F satisfies (AC1) if dim im A ≥ k for every A ∈ K_F.
    Definition. *)
Definition dgpr_AC1 (F : Hom Rn Rn -> R) : Prop :=
  forall A, dgpr_KF F A -> linear_rank_at_least A k.

(** Source for [is_dgpr_lambda]: blueprint def:BF,
    λ(F) = inf { sv_k(A) : A ∈ K_F }, characterised as the greatest lower
    bound. Definition. *)
Definition is_dgpr_lambda (F : Hom Rn Rn -> R) (l : R) : Prop :=
  (forall A, dgpr_KF F A -> l <= sv A) /\
  forall l', (forall A, dgpr_KF F A -> l' <= sv A) -> l' <= l.

(** Source for [is_dgpr_Lambda]: blueprint def:BF,
    Λ(F) = sup { |A| : A ∈ K_F }, characterised as the least upper bound.
    Definition. *)
Definition is_dgpr_Lambda (F : Hom Rn Rn -> R) (L : R) : Prop :=
  (forall A, dgpr_KF F A -> NH A <= L) /\
  forall L', (forall A, dgpr_KF F A -> NH A <= L') -> L <= L'.

(** Source for [dgpr_lambda_unique]: blueprint def:BF, the infimum
    λ(F) is unique. Supporting lemma. *)
Lemma dgpr_lambda_unique F l l' : is_dgpr_lambda F l -> is_dgpr_lambda F l' -> l = l'.
Proof.
move=> [h1 h2] [h1' h2']; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: h2' h1.
- exact: h2 h1'.
Qed.

(** Source for [dgpr_Lambda_unique]: blueprint def:BF, the supremum
    Λ(F) is unique. Supporting lemma. *)
Lemma dgpr_Lambda_unique F L L' : is_dgpr_Lambda F L -> is_dgpr_Lambda F L' -> L = L'.
Proof.
move=> [h1 h2] [h1' h2']; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: h2 h1'.
- exact: h2' h1.
Qed.

(** Source for [dgpr_sv_continuous]: blueprint proof of lem:KF, sv_k is
    continuous on Hom(R^n, R^n) by lem:sv(lip) and ‖A‖ ≤ |A| (Federer
    1.7.9, p. 35). Supporting lemma. *)
Lemma dgpr_sv_continuous :
  continuous (fun A : real_norm_metric_space hNH => (sv A : real_line_metric R)).
Proof.
apply: dgpr_local_lipschitz_continuous => c.
exists 1, 1; split=> // y _.
rewrite real_line_metric_distanceE mul1r real_norm_metric_distanceE.
apply: le_trans (dgpr_sv_lip hBn hBn hbn hk c y) _.
exact: (hom_operator_norm_comparison hBn hBn hbn (c - y)).1.
Qed.

Section Integrand.
Variable F : Hom Rn Rn -> R.
Hypothesis hF : @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1.

(** Source for [dgpr_B_image_compact]: blueprint proof of lem:KF:
    B_F[G(n, k)] is compact, being the image of the compact set G(n, k)
    (Allard 2.3) under the continuous map B_F. Supporting lemma. *)
Lemma dgpr_B_image_compact : compact (dgpr_B k F @` G : set (real_norm_metric_space hNH)).
Proof.
have -> : (dgpr_B k F @` G : set (real_norm_metric_space hNH)) =
    (fun S : GA => (dgpr_B k F (set_val S) : real_norm_metric_space hNH)) @` setT.
  apply/seteqP; split=> [_ [S hS <-]|_ [S _ <-]].
  - by exists (projection_grassmann_of hS).
  - by exists (set_val S) => //; exact: set_valP.
apply: continuous_compact; last exact: @projection_grassmann_compact R n k.
exact: continuous_subspaceT (dgpr_B_continuous hF).
Qed.

(** Source for [dgpr_KF_compact_convex]: blueprint lem:KF, first
    sentence: K_F is compact and convex, by lem:hull. *)
Theorem dgpr_KF_compact_convex :
  compact (dgpr_KF F : set (real_norm_metric_space hNH)) /\ is_inner_convex (dgpr_KF F).
Proof.
split; last exact: convex_hull_convex.
have [m [u hu]] := hom_space_finite_basis hbn hbn.
exact: (dgpr_hull_compact hu dgpr_B_image_compact).
Qed.

(** Source for [dgpr_KF_nonempty]: K_F is nonempty, since G(n, k) is
    nonempty for k ≤ n (Allard 2.3). Supporting lemma. *)
Lemma dgpr_KF_nonempty : exists A, dgpr_KF F A.
Proof.
have /andP [_ hkn] := hk.
have [S0 _] := @projection_grassmann_point R n k hkn.
exists (dgpr_B k F (set_val S0)); apply: convex_hull_includes.
by exists (set_val S0) => //; exact: set_valP.
Qed.

(** Source for [dgpr_B_KF]: blueprint def:BF, B_F(S) ∈ K_F for
    S ∈ G(n, k). Supporting lemma. *)
Lemma dgpr_B_KF S : G S -> dgpr_KF F (dgpr_B k F S).
Proof. by move=> hS; apply: convex_hull_includes; exists S. Qed.

(** Source for [dgpr_KF_lambda]: blueprint proof of lem:KF: under
    (AC1), sv_k attains a positive minimum on the compact set K_F, by
    lem:sv(rank) and the continuity of sv_k; hence λ(F) exists and
    λ(F) > 0. *)
Theorem dgpr_KF_lambda : dgpr_AC1 F -> exists2 l, is_dgpr_lambda F l & 0 < l.
Proof.
move=> hAC.
have [hc _] := dgpr_KF_compact_convex.
have [A0 hA0] := dgpr_KF_nonempty.
have hcont : continuous (fun A : real_norm_metric_space hNH => (sv A : R^o)) := dgpr_sv_continuous.
have hne : (dgpr_KF F : set (real_norm_metric_space hNH)) !=set0 by exists A0.
have [c hcK hmin] := compact_EVT_min hne hc (continuous_subspaceT hcont).
have hcK' : dgpr_KF F c by move: hcK; rewrite inE.
exists (sv c).
- split=> [A hA|l' hl']; last exact: hl'.
  by apply: hmin; rewrite inE.
- exact/(dgpr_sv_rank hBn hBn hbn hk c).2/hAC.
Qed.

(** Source for [dgpr_KF_Lambda]: blueprint proof of lem:KF: the norm
    attains a maximum on the compact set K_F; hence Λ(F) exists and is
    finite. *)
Theorem dgpr_KF_Lambda : exists L, is_dgpr_Lambda F L.
Proof.
have [hc _] := dgpr_KF_compact_convex.
have [A0 hA0] := dgpr_KF_nonempty.
have hcont : continuous (fun A : real_norm_metric_space hNH => (NH A : R^o)) :=
  @real_norm_metric_norm_continuous R _ _ hNH.
have hne : (dgpr_KF F : set (real_norm_metric_space hNH)) !=set0 by exists A0.
have [c hcK hmax] := compact_EVT_max hne hc (continuous_subspaceT hcont).
have hcK' : dgpr_KF F c by move: hcK; rewrite inE.
exists (NH c); split=> [A hA|L' hL']; last exact: hL'.
by apply: hmax; rewrite inE.
Qed.

(** Source for [dgpr_KF_bounds]: blueprint lem:KF, second sentence: if
    F satisfies (AC1), then 0 < λ(F) ≤ Λ(F), sv_k(A) ≥ λ(F) and
    |A| ≤ Λ(F) for A ∈ K_F. The inequality λ(F) ≤ Λ(F) follows from
    sv_k(A) ≤ ‖A‖ ≤ |A|. *)
Theorem dgpr_KF_bounds l L : dgpr_AC1 F -> is_dgpr_lambda F l -> is_dgpr_Lambda F L ->
  [/\ 0 < l, l <= L & forall A, dgpr_KF F A -> l <= sv A /\ NH A <= L].
Proof.
move=> hAC hl hL.
have [l0 hl0 hpos] := dgpr_KF_lambda hAC.
have <- := dgpr_lambda_unique hl0 hl.
have [A0 hA0] := dgpr_KF_nonempty.
split=> //.
- apply: le_trans (hl0.1 _ hA0) _; apply: le_trans (dgpr_sv_le_hom_norm hBn hBn hbn hk A0) _.
  exact: hL.1.
- move=> A hA; split; [exact: hl0.1 | exact: hL.1].
Qed.

(** Source for [dgpr_lemma_KF]: blueprint lem:KF, second sentence,
    with the existence of λ(F) and Λ(F). *)
Theorem dgpr_lemma_KF : dgpr_AC1 F ->
  exists l L, [/\ is_dgpr_lambda F l, is_dgpr_Lambda F L, 0 < l, l <= L &
    forall A, dgpr_KF F A -> l <= sv A /\ NH A <= L].
Proof.
move=> hAC.
have [l hl _] := dgpr_KF_lambda hAC.
have [L hL] := dgpr_KF_Lambda.
have [h1 h2 h3] := dgpr_KF_bounds hAC hl hL.
by exists l, L; split.
Qed.

End Integrand.
End KF.
