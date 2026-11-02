(** Federer (1969), 3.2.28(4), printed p. 266:
    the differential of the square map is isometric on
    the actual tangent and therefore has intrinsic
    tangent-dimensional Jacobian one, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerProductRestriction InnerNorm OrthogonalMaps
  ExteriorGrading ExteriorMaps ExteriorNorm ExteriorNormNaturality FiniteExteriorPowers
  EuclideanLinearJacobian EuclideanTopExteriorVolume EuclideanStiefelInnerSplitting
  FiniteInnerChartUP FiniteInnerChart PartialFunctionUP PartialExteriorNormUP
  PartialExteriorIsometricChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_orthogonal_top_jacobian_one]: the
    tangent isometry gives Jacobian one in Federer
    3.2.28(4), p. 266, by 1.7.5–1.7.6,
    pp. 32–34. The unit top exterior word proves
    the actual value, including its empty-word boundary. *)
Lemma euclidean_orthogonal_top_jacobian_one (R:realType) m n
    (H:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (hom_as_linear H) ->euclidean_linear_jacobian m H= 1.
Proof.
move=>hH.
pose z:=e_lambda (@coordinate_basis R m) (ord_tuple m).
have hUnit:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) z= 1:=
  orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m)
    (@euclidean_coordinate_orthonormal_family R m).
have hScale:=euclidean_top_exterior_volume_scale H z.
rewrite (exterior_norm_orthogonal_natural (euclidean_two_nonzero R)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) hH) hUnit mulr1 in hScale.
exact:esym hScale.
Qed.

(** Source for [tangent_isometry_partial_jacobian_one]: the
    full intrinsic tangent-dimensional Jacobian calculation
    in Federer 3.2.28(4), p. 266. The partial
    graph has exactly the actual tangent plane as its
    domain. Isometric coordinates are proved to exist
    and no value outside that plane affects the norm. *)
Theorem tangent_isometry_partial_jacobian_one (R:realType) n p mu
    (T:G (R_n R n) mu) (L:Hom (R_n R n) (R_n R p))
    (d:partial_function (R_n R n) (R_n R p)):
  (forall x y,grassmann_val T x ->grassmann_val T y ->
    euclidean_inner_product (L x) (L y)=euclidean_inner_product x y) ->
  (forall v w,partial_function_graph d v w <->grassmann_val T v /\L v=w) ->
  is_partial_exterior_norm mu d 1.
Proof.
move=>hPair hGraph.
pose S:=grassmann_val T.
pose V:=subspace_space S.
pose B:=@restricted_inner_product R (R_n R n) (@euclidean_inner_product R n) S.
pose hB:=restricted_inner_productP (@euclidean_inner_productP R n) S.
have [b hb]:=grassmann_proof T.
have [a [q hChart]]:=finite_inner_chart_exists hB hb.
pose D:=hom_comp (hom_of_linear (subspace_inclusion S)) a.
pose H:=hom_comp L D.
have hD:is_orthogonal_map (@euclidean_inner_product R mu) (@euclidean_inner_product R n)
    (hom_as_linear D).
  move=>x y; exact:finite_inner_chart_product hChart x y.
have hH:is_orthogonal_map (@euclidean_inner_product R mu) (@euclidean_inner_product R p)
    (hom_as_linear H).
  move=>x y.
  change (euclidean_inner_product (L (D x)) (L (D y))=euclidean_inner_product x y).
  rewrite hPair; [exact:hD|exact:subspace_valP (a x)|exact:subspace_valP (a y)].
have hCoords v w:partial_function_graph d v w <->exists x,D x=v /\H x=w.
  split.
  - move=>hd; have [hv hw]:=(hGraph v w).1 hd.
    pose z:=@subspace_lift R (R_n R n) S v hv.
    exists (q z).
    have hDv:D (q z)=v.
      change (subspace_val (a (q z))=v).
      by rewrite (finite_inner_chart_right_inverse hChart).
    split; first exact hDv.
    change (L (D (q z))=w); by rewrite hDv.
  - move=>[x [hx hw]]; apply:(hGraph v w).2; split.
    + rewrite -hx; exact:subspace_valP (a x).
    + rewrite -hx; exact hw.
have hNorm:=@partial_exterior_isometric_chart_norm R mu n p mu D H d hD hCoords.
by rewrite (euclidean_orthogonal_top_jacobian_one hH) in hNorm.
Qed.
