(** Private orthogonal-chart existence proof supporting Federer (1969),
    2.10.30, p. 195. Transitivity on one-dimensional orthogonal injections
    gives a map sending the specified coordinate axis to the normal;
    finite-dimensional orthogonality supplies its two-sided linear inverse.
    These are already proved project results, not external linear algebra.
    Source context: EuclideanNormalChartUP.v and the annotated
    orthogonal-frame and transitivity declarations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  OrthonormalFamilies CoordinateProjection OrthogonalMaps OrthonormalFrameMap
  OrthogonalInjectionSpaces OrthogonalFinite EuclideanNormalChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_normal_chart_exists]: supporting existence of
    general-direction orthogonal coordinates for 2.10.30, p. 195 The chart
    is hidden after its abstract laws have been established. *)
Theorem euclidean_normal_chart_exists (R : realType) n (j : 'I_n) (u : R_n R n) :
  euclidean_inner_product u u= 1 ->
  exists D : euclidean_normal_chart_data R n, @is_euclidean_normal_chart R n j u D.
Proof.
move=> hu.
pose V := R_n R n.
pose B := @euclidean_inner_product R n.
pose e := @coordinate_basis R n j.
have he : B e e= 1 by rewrite /B euclidean_inner_basis /e /coordinate_basis ffunE eqxx.
have ho0 : orthonormal_family B (fun _ : 'I_1=>e).
  by move=> i k; rewrite (ord1 i) (ord1 k) eqxx he.
have ho1 : orthonormal_family B (fun _ : 'I_1=>u).
  by move=> i k; rewrite (ord1 i) (ord1 k) eqxx /B hu.
have [f0 [hf0 hf0e]] := @orthonormal_frame_map_exists R V B
  (@euclidean_inner_productP R n) 1 (fun _ : 'I_1=>e) ho0.
have [f1 [hf1 hf1e]] := @orthonormal_frame_map_exists R V B
  (@euclidean_inner_productP R n) 1 (fun _ : 'I_1=>u) ho1.
have [f [hf hff]] := @orthogonal_injection_transitive R (R_n R 1) V
  (@euclidean_inner_product R 1) B (@euclidean_inner_productP R 1)
  (@euclidean_inner_productP R n) 1 (@coordinate_basis R 1) n
  (@coordinate_basis R n) (@coordinate_basisP R 1) (@coordinate_basisP R n)
  f0 f1 hf0 hf1.
have [g [hfg [hgf hg]]] := @orthogonal_endomorphism_inverse_exists R V B
  (@euclidean_inner_productP R n) n (@coordinate_basis R n)
  (@coordinate_basisP R n) f hf.
have haxis : f e=u.
  by rewrite -(hf0e ord0) hff hf1e.
exists (@Build_euclidean_normal_chart_data R n f g); constructor=> //.
Qed.
