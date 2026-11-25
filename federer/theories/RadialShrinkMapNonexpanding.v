(** Federer (1969), 4.1.15, p. 372: the sharp global
    Lipschitz bound for the original radial shrink map.
    The two outer cases use Federer's printed square
    calculation; the mixed cases use 1.7.1's reverse
    triangle inequality. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals classical_sets topology lra.
From Federer Require Import RealNormUP NormMetric InnerNorm InnerNormDifferential
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP RadialShrinkMapUP RadialShrinkMapDisplacement
  RadialShrinkMapNorm RadialShrinkMapPairSquares.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section RadialShrinkMapNonexpanding.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm hB).
Local Notation hN := (inner_norm_real_norm hB).
Variable r : R.
Hypothesis hr : 0<r.
Variable P : X -> X.
Hypothesis hP : is_radial_shrink_map r P.

(** Source for [radial_shrink_mixed_distance_bound]: the
    omitted mixed inside/outside case needed for the
    global bound in Federer 4.1.15, p. 372. *)
Lemma radial_shrink_mixed_distance_bound a b :
  N a<=r -> r<=N b -> N (P a-P b)<=N (a-b).
Proof.
move=> ha hb.
rewrite (radial_shrink_closed_inner hr hP ha) sub0r inner_normN
  (radial_shrink_outer_norm hr hP hb).
have hReverse := inner_norm_reverse_triangle hB b a.
rewrite -[b-a]opprB inner_normN in hReverse.
have hOrder : 0<=N b-N a by lra.
rewrite (ger0_norm hOrder) in hReverse.
lra.
Qed.

(** Source for [radial_shrink_nonexpanding]: the literal
    Lip(Psi_r)<= 1 assertion in 4.1.15, p. 372,
    including the boundary sphere and zero-dimensional target. *)
Theorem radial_shrink_nonexpanding a b :
  N (P a-P b)<=N (a-b).
Proof.
case:(leP (N a) r)=> ha; case:(leP (N b) r)=> hb.
- rewrite (radial_shrink_closed_inner hr hP ha)
    (radial_shrink_closed_inner hr hP hb) subrr inner_norm0.
  exact:inner_norm_nonnegative.
- exact:radial_shrink_mixed_distance_bound ha (ltW hb).
- have hSwap := radial_shrink_mixed_distance_bound hb (ltW ha).
  by rewrite -[P b-P a]opprB -[b-a]opprB !inner_normN in hSwap.
- rewrite -(ler_sqr (inner_norm_nonnegative hB _)
    (inner_norm_nonnegative hB _)).
  have hDifference := radial_shrink_outer_pair_difference_nonpositive
    hr hP (ltW ha) (ltW hb).
  lra.
Qed.

(** Source for [radial_shrink_lipschitz_bound]: the same
    sharp bound in the original Lipschitz interface of
    2.2.7, as asserted in 4.1.15, p. 372. *)
Theorem radial_shrink_lipschitz_bound :
  @is_metric_lipschitz_bound R (real_norm_metric_space hN)
    (real_norm_metric_space hN) setT P 1.
Proof.
split; first exact:ler01.
move=> a b _ _.
change (is_true (N (P a-P b)<= 1*N (a-b))).
by rewrite mul1r; exact:radial_shrink_nonexpanding.
Qed.
End RadialShrinkMapNonexpanding.
