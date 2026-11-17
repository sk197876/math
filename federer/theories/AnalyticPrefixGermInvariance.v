(** Federer (1969), 3.4.8(6), p. 329:
    actual analytic pullback by a fixed-tail linear
    map preserves the original coordinate subring Q_p.
    The exact original square and representative laws
    prove the assertion; it is not a premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormAnalyticUP AnalyticGermUP AnalyticGermRing
  PointedAnalyticPullbackUP PointedAnalyticPullbackSealed PointedAnalyticImagePreservation
  AnalyticPrefixCoordinatesSealed AnalyticPrefixMapRegularity AnalyticPrefixGermMap
  AnalyticPrefixGermMapLaws AnalyticPrefixGermSubring AnalyticPrefixFixedTailSquare.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_germ_subring_invariant]: the
    original Q_p is preserved by the actual maps
    fixing the tail, as used in 3.4.8(6), p. 329. *)
Theorem analytic_prefix_germ_subring_invariant (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) p (hPN:(p<=n)%N) (H:Hom X X)
  (M:@analytic_germ_ring R X NX hNX 0->@analytic_germ_ring R X NX hNX 0):
  (forall i k,omega i (e k) = if i==k then 1 else 0) ->
  is_pointed_analytic_germ_pullback H M ->
  (forall i:'I_n,(p<=i)%N ->H (e i) = e i) ->
  forall alpha,@analytic_prefix_germ_subring R X NX hNX n e he omega p hPN alpha ->
    @analytic_prefix_germ_subring R X NX hNX n e he omega p hPN (M alpha).
Proof.
move=>hDual hM hFixed alpha /analytic_prefix_germ_subring_membership[beta <-].
pose Y:=R_n R p.
pose NY:=inner_norm (@euclidean_inner_productP R p).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R p).
pose projection:=@AnalyticPrefixCoordinates.projection R X n omega p hPN.
pose section:=@AnalyticPrefixCoordinates.inclusion R X n e p hPN.
pose P:=@analytic_prefix_germ_map R X NX hNX n e he omega p hPN.
have hSection:@norm_analytic_at R Y X NY NX hNY hNX setT section 0:=
  (@analytic_prefix_inclusion_analytic R X NX hNX p section) 0 Logic.I.
have hSectionZero:section 0 = 0:=linear0 section.
pose S:=@PointedAnalyticPullback.map R Y X NY NX hNY hNX setT section 0 0 hSection hSectionZero.
have hS:=@PointedAnalyticPullback.laws R Y X NY NX hNY hNX setT section 0 0 hSection hSectionZero.
have hP:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega p hPN.
have hSquare:=@analytic_prefix_fixed_tail_square R X n e he omega p hPN projection section H hDual
  (@AnalyticPrefixCoordinates.projection_laws R X n omega p hPN)
  (@AnalyticPrefixCoordinates.inclusion_laws R X n e p hPN) hFixed.
apply/analytic_prefix_germ_subring_membership;exists (S (M (P beta))).
exact:(@pointed_analytic_image_preservation R X Y NX NY hNX hNY 0 0
  projection section H P S M hP hS hM hSquare beta).
Qed.
