(** Federer (1969), 3.2.36, p. 273: intrinsic volumes
    are unchanged by arbitrary actual metric isometric injections. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear OrthogonalMaps GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CompactHausdorffMetric CompactSetDistanceProfile CompactMetricBounded IntegralGeometricGauge SteinerTubePolynomial
  MetricIsometricInjectionAffine MetricIsometricConvexImage MetricIsometricImageGeometry
  EuclideanEmbeddingAmbientExtension EuclideanBlockLinearMaps EuclideanBlockMetricIsometries
  AffineOrthogonalBijection CompactConvexIsometryIntrinsicVolumes CanonicalEmbeddingIntrinsicVolumes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_isometric_embedding_intrinsic_volume]:
    the assertion about isometric injections in Federer 3.2.36,
    p. 273, first on nonempty compact convex bodies. The arbitrary
    original metric map is proved affine; its orthogonal linear part
    extends locally in the common space R^(m+n). The actual ambient
    affine isometry, proved tube-coefficient invariance and convolution
    with actual singleton factors identify the two original intrinsic
    volumes. No preassigned affine structure or source/target dimension
    inequality is assumed. Degree zero and both empty blocks remain. *)
Theorem compact_convex_isometric_embedding_intrinsic_volume (R:realType) m n k
    (hkm:(k<=m)%N) (hkn:(k<=n)%N)
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_inner_convex (val A) ->(forall x y,mdist (f x) (f y)=mdist x y) ->
  @integral_geometric_gauge R n k hkn 1 (f @` val A)=
    @integral_geometric_gauge R m k hkm 1 (val A).
Proof.
move=>hA hMetric.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose Z:=inner_metric_space (@euclidean_inner_productP R (m+n)).
have [hLinear hPair]:=@metric_isometric_injection_linear_part R (R_n R m) (R_n R n)
  _ _ (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) f hMetric.
pose g:Hom (R_n R m) (R_n R n):=
  @HomMap R (R_n R m) (R_n R n) (fun x=>f x-f 0) (introT (asboolP _) hLinear).
have hG:is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g).
  exact hPair.
have [T [hT hExtension]]:=euclidean_embedding_ambient_extension hG.
pose a:Z:=@euclidean_last_injection R m n (f 0).
pose F:Z->Z:=fun z=>a+T z.
have [G [hGF [hFG hFMetric]]]:=affine_orthogonal_bijection_inverse a hT.
have hCommuting x:F (@euclidean_first_injection R m n x)=@euclidean_last_injection R m n (f x).
  rewrite /F hExtension /a.
  rewrite -(@linD R (R_n R n) (R_n R (m+n)) (@euclidean_last_injection R m n)
    (@euclidean_last_injection_linear R m n) (f 0) (g x)).
  congr (@euclidean_last_injection R m n _).
  change (f 0+(f x-f 0)=f x); by rewrite addrC subrK.
have [B hImage]:=@metric_isometric_compact_image_exists R X Y f A hMetric.
have hB:is_inner_convex (val B).
  rewrite hImage; exact:(@metric_isometric_convex_image R (R_n R m) (R_n R n) _ _
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) f (val A) hMetric hA).
have [C hFirst]:=@metric_isometric_compact_image_exists R X Z (@euclidean_first_injection R m n) A
  (@euclidean_first_injection_metric R m n).
have [D hLast]:=@metric_isometric_compact_image_exists R Y Z (@euclidean_last_injection R m n) B
  (@euclidean_last_injection_metric R m n).
have hC:is_inner_convex (val C).
  rewrite hFirst; exact:(@metric_isometric_convex_image R (R_n R m) (R_n R (m+n)) _ _
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R (m+n))
    (@euclidean_first_injection R m n) (val A) (@euclidean_first_injection_metric R m n) hA).
have hD:is_inner_convex (val D).
  rewrite hLast; exact:(@metric_isometric_convex_image R (R_n R n) (R_n R (m+n)) _ _
    (@euclidean_inner_productP R n) (@euclidean_inner_productP R (m+n))
    (@euclidean_last_injection R m n) (val B) (@euclidean_last_injection_metric R m n) hB).
have hImages:val D=F @` val C.
  rewrite hLast hImage hFirst; apply/seteqP; split.
  - move=>z [y [x hx <-] <-]; exists (@euclidean_first_injection R m n x).
    + by exists x.
    + exact:hCommuting.
  - move=>z [y [x hx <-] <-]; rewrite hCommuting.
    exists (f x)=>//; by exists x.
have hInvariant:=@compact_convex_isometry_intrinsic_volumes R (m+n) C D F G
  hC hD hImages hGF hFG hFMetric.
have hkTotal:(k<=m+n)%N:=leq_trans hkm (leq_addr n m).
pose l:'I_(m+n).+1:=Ordinal (leq_ltn_trans hkTotal (ltnSn (m+n))).
have hCoeff:@integral_geometric_gauge R (m+n) k hkTotal 1 (val D)=
    @integral_geometric_gauge R (m+n) k hkTotal 1 (val C).
  rewrite (bool_irrelevance hkTotal (steiner_dimension_guard l)); exact:hInvariant l.
have hSource:=@first_canonical_embedding_intrinsic_volume R m n k hkm hkTotal (val A)
  (set_valP A).2 hA (compact_metric_diameter_finite A).
have hTarget:=@last_canonical_embedding_intrinsic_volume R m n k hkn hkTotal (val B)
  (set_valP B).2 hB (compact_metric_diameter_finite B).
rewrite -hImage -hTarget -hSource -hFirst -hLast.
exact hCoeff.
Qed.
