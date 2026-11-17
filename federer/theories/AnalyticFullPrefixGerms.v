(** Federer (1969), 3.4.8(1),(8), pp. 326, 329:
    the full prefix gives the whole original
    germ ring. Reuse the actual full-prefix
    inverse equations and pointed germ retraction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct AnalyticGermUP AnalyticGermRing
  AnalyticPrefixCoordinatesSealed AnalyticPrefixMapRegularity AnalyticPrefixSphereCoordinates
  AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticPrefixGermSubring
  PointedAnalyticPullbackSealed PointedAnalyticPullbackRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_full_prefix_germ_map_surjective]:
    Q_n is the original whole germ ring,
    3.4.8(1),(8), pp. 326, 329. The
    original coordinate isomorphism supplies a
    genuine analytic section, including dimension zero. *)
Theorem analytic_full_prefix_germ_map_surjective (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k) = if i==k then 1 else 0):
  forall alpha:@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0,
    exists beta,@analytic_prefix_germ_map R X (inner_norm hB) (inner_norm_real_norm hB)
      n e he omega n (leqnn n) beta = alpha.
Proof.
pose NX:=inner_norm hB.
pose hNX:=inner_norm_real_norm hB.
pose Y:=R_n R n.
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose P:=@AnalyticPrefixCoordinates.projection R X n omega n (leqnn n).
pose S:=@AnalyticPrefixCoordinates.inclusion R X n e n (leqnn n).
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega n (leqnn n).
have hP:=@AnalyticPrefixCoordinates.projection_laws R X n omega n (leqnn n).
have hS:=@AnalyticPrefixCoordinates.inclusion_laws R X n e n (leqnn n).
have hInverse x:S (P x) = x.
  apply:(@analytic_prefix_section_projection_fixed R X B hB n e he hON omega hDual n (leqnn n) P S hP hS x).
  move=>i hN;have hFalse:=leq_ltn_trans hN (ltn_ord i);by rewrite ltnn in hFalse.
have hAnalytic:=(@analytic_prefix_inclusion_analytic R X NX hNX n S) 0 Logic.I.
pose T:=@PointedAnalyticPullback.map R Y X NY NX hNY hNX setT S 0 0 hAnalytic (linear0 S).
have hT:=@PointedAnalyticPullback.laws R Y X NY NX hNY hNX setT S 0 0 hAnalytic (linear0 S).
have hE:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega n (leqnn n).
move=>alpha;exists (T alpha).
exact:(@pointed_analytic_germ_pullback_retraction R Y X NY NX hNY hNX 0 0 S P T E hT hE hInverse alpha).
Qed.
