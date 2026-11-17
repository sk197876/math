(** Federer (1969), 3.4.8(8), p. 329:
    the original last coordinate splits off
    from the preceding coordinate prefix. Apply
    the existing dual-basis, prefix isometry and
    finite linear bound results to the exact
    transverse laws of 3.4.6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP LinearBasis FiniteCoordinates GrassmannAbbreviations
  InnerProductUP InnerNorm InnerDualBasis HilbertFormCompactness OrthonormalFamilies OrthonormalParseval
  EuclideanInnerProduct EuclideanCoordinateTopology Annihilator FiniteDualDimension DualityAnnihilator
  NormFiniteLinearBound WeierstrassTransverseUP AnalyticPrefixCoordinatesUP
  AnalyticPrefixCoordinateLaws AnalyticPrefixSphereCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_last_coordinate_prefix_split]:
    the original e_j, omega_j and p_(j-1)
    in the repeated preparation of 3.4.8(8),
    p. 329, satisfy the full transverse
    specification. No coordinate kernel or norm
    identification is added as a premise. *)
Theorem analytic_last_coordinate_prefix_split (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) j (e:'I_j.+1->X) (he:is_basis e)
  (hON:orthonormal_family B e) (omega:'I_j.+1->Hom X R^o)
  (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  (P:Hom X (R_n R j)) (S:Hom (R_n R j) X):
  is_analytic_prefix_projection omega (leqnSn j) P ->
  is_analytic_prefix_section e (leqnSn j) S ->
  is_weierstrass_transverse_space (inner_norm hB)
    (inner_norm (@euclidean_inner_productP R j)) (e ord_max) (omega ord_max) S P.
Proof.
move=>hP hS.
have hOmega i:omega i = dual_basis he i:=biorthogonal_basis_unique he hDual i.
have hProjection (x:X):S (P x) = x-(omega ord_max x)*:e ord_max.
  have hSP:S (P x) = \sum_(i<j) omega (widen_ord (leqnSn j) i) x*:e (widen_ord (leqnSn j) i).
    rewrite -(euclidean_coordinate_expansion (P x)) linear_sum /=.
    apply:eq_bigr=>i _;by rewrite linearZ /= hS hP.
  have hExpansion:x = \sum_(i<j.+1) omega i x*:e i.
    rewrite {1}(basis_vector_expansion he x);apply:eq_bigr=>i _;by rewrite hOmega.
  have hDecomposition:x = (\sum_(i<j) omega (widen_ord (leqnSn j) i) x*:
      e (widen_ord (leqnSn j) i))+(omega ord_max x)*:e ord_max.
    by rewrite {1}hExpansion big_ord_recr.
  have hRestore:x-(omega ord_max x)*:e ord_max =
      \sum_(i<j) omega (widen_ord (leqnSn j) i) x*:e (widen_ord (leqnSn j) i).
    by rewrite {1}hDecomposition addrK.
  exact:etrans hSP (esym hRestore).
constructor.
- by rewrite hDual eqxx.
- move=>y;rewrite hOmega (@orthonormal_basis_inner_coordinate R X B hB
    [the finType of 'I_j.+1] e hON he ord_max (S y)).
  exact:(@analytic_prefix_section_tail_orthogonal R X B hB j.+1 e hON j (leqnSn j) S hS y ord_max (leqnn j)).
- exact:hProjection.
- exact:(@analytic_prefix_projection_section R X j.+1 e omega j (leqnSn j) P S hDual hP hS).
- exact:(@analytic_prefix_section_norm R X B hB j.+1 e hON j (leqnSn j) S hS).
- exact:(@norm_finite_linear_bounded R (R_n R j) X
    (inner_norm (@euclidean_inner_productP R j)) (inner_norm hB)
    (inner_norm_real_norm (@euclidean_inner_productP R j)) (inner_norm_real_norm hB)
    j (@coordinate_basis R j) (@coordinate_basisP R j) S).
- exact:(@norm_finite_linear_bounded R X (R_n R j)
    (inner_norm hB) (inner_norm (@euclidean_inner_productP R j))
    (inner_norm_real_norm hB) (inner_norm_real_norm (@euclidean_inner_productP R j)) j.+1 e he P).
Qed.
