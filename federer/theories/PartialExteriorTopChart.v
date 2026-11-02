(** Federer (1969), 3.2.20, p. 257: the top-degree
    exterior norm of a partial map in an injective linear chart.
    Top exterior volume scaling gives the printed Jacobian product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorGrading FiniteExteriorPowers
  ExteriorMaps ExteriorOperatorEstimate EuclideanLinearJacobian EuclideanTopExteriorVolume
  PartialFunctionUP PartialExteriorNormUP ModuleQuotient SubspaceCarrier SubspaceSums
  GrassmannSubspaces EuclideanLinearRangePlane InnerProductRestriction
  LinearBasis OrthonormalFamilies OrthonormalisationUP GramSchmidt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_exterior_chart_word_scale]: supporting word
    identity in the Jacobian product of Federer 3.2.20, p. 257.
    In an injective m-dimensional source chart D, image word lengths
    scale by J_m(H)/J_m(D). This is 1.7.6, p. 34,
    applied to the two top exterior maps; no ambient values of d occur. *)
Lemma partial_exterior_chart_word_scale (R : realType) m n k
    (D : Hom (R_n R m) (R_n R n)) (H : Hom (R_n R m) (R_n R k))
    (d : partial_function (R_n R n) (R_n R k)) :
  injective D ->
  (forall v w, partial_function_graph d v w <-> exists x, D x=v /\ H x=w) ->
  forall (v : 'I_m -> R_n R n) (w : 'I_m -> R_n R k),
    (forall i, partial_function_graph d (v i) (w i)) ->
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R k)
      (e_lambda w (ord_tuple m))=
    (euclidean_linear_jacobian m H/euclidean_linear_jacobian m D)*
      exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
        (e_lambda v (ord_tuple m)).
Proof.
move=> hInj hGraph v w hVW.
have hPos := (euclidean_linear_jacobian_top_positive D).2 hInj.
have hex i := (hGraph (v i) (w i)).1 (hVW i).
have [x hx] := choice hex.
have hD : (fun i=>D (x i))=v by apply: funext=> i; exact: (hx i).1.
have hH : (fun i=>H (x i))=w by apply: funext=> i; exact: (hx i).2.
have hSource := @euclidean_top_exterior_volume_scale R m n D (e_lambda x (ord_tuple m)).
have hTarget := @euclidean_top_exterior_volume_scale R m k H (e_lambda x (ord_tuple m)).
rewrite exterior_map_indexed_product hD in hSource.
rewrite exterior_map_indexed_product hH in hTarget.
by rewrite hTarget hSource mulrA divfK ?gt_eqF.
Qed.

(** Source for [partial_exterior_norm_injective_chart]: the linear
    norm calculation underlying ap J_m f times J_m psi equals
    J_m(F composed with psi), Federer 3.2.20, p. 257.
    An orthonormal basis of the actual differential image supplies a
    unit exterior word attaining the bound. All natural source dimensions,
    including zero, are covered without an extra rank hypothesis. *)
Theorem partial_exterior_norm_injective_chart (R : realType) m n k
    (D : Hom (R_n R m) (R_n R n)) (H : Hom (R_n R m) (R_n R k))
    (d : partial_function (R_n R n) (R_n R k)) :
  injective D ->
  (forall v w, partial_function_graph d v w <-> exists x, D x=v /\ H x=w) ->
  is_partial_exterior_norm m d (euclidean_linear_jacobian m H/euclidean_linear_jacobian m D).
Proof.
move=> hInj hGraph.
pose C := euclidean_linear_jacobian m H/euclidean_linear_jacobian m D.
have hPos := (euclidean_linear_jacobian_top_positive D).2 hInj.
have hInv : 0<=(euclidean_linear_jacobian m D)^-1 by rewrite invr_ge0; exact: ltW hPos.
have hC : 0<=C := mulr_ge0 (@euclidean_linear_jacobian_nonnegative R m k m H) hInv.
have hScale := @partial_exterior_chart_word_scale R m n k D H d hInj hGraph.
constructor; first exact hC.
- move=> v w hVW hUnit; rewrite (hScale v w hVW).
  apply: (le_trans (ler_wpM2l hC hUnit) _); by rewrite mulr1.
- move=> L hL hBound.
  have [P hRange] := euclidean_injective_range_plane hInj.
  have [e he] := grassmann_proof P.
  pose hP := @restricted_inner_productP R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) (grassmann_val P).
  have [u [_ hOrtho]] := orthonormal_basis_exists hP he.
  pose v i := subspace_val (u i).
  have hVO : orthonormal_family (@euclidean_inner_product R n) v.
    exact: orthonormalisation_orthonormal hOrtho.
  have hex i : exists x : R_n R m, D x=v i.
    have hMem : range D (v i).
      rewrite hRange; exact: subspace_valP (u i).
    have [x _ hx] := hMem; by exists x.
  have [x hx] := choice hex.
  pose w i := H (x i).
  have hVW i : partial_function_graph d (v i) (w i).
    apply: (hGraph (v i) (w i)).2; exists (x i); by split.
  have hUnit := orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) hVO.
  have hUnitLe : exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (e_lambda v (ord_tuple m))<=1 by rewrite hUnit.
  have hTest := hBound v w hVW hUnitLe.
  by rewrite (hScale v w hVW) hUnit mulr1 in hTest.
Qed.
