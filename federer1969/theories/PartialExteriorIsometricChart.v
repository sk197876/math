(** Federer (1969), 3.2.22, pp. 258–259: the
    intrinsic exterior norm of an actual partial linear graph
    in orthonormal coordinates, in every exterior degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian OrthogonalMaps PartialFunctionUP
  PartialExteriorNormUP FiniteExteriorPowers ExteriorNorm ExteriorMaps ExteriorOperatorEstimate
  ExteriorNormNaturality ExteriorOperatorNorm OperatorNormUP ExteriorUnitWordOperatorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partial_exterior_isometric_chart_norm]:
    the exterior-norm comparison in Federer 3.2.22,
    p. 259, becomes equality in isometric coordinates.
    Only the actual partial graph is used, with no off-plane
    values. The simple-word characterization of the induced
    exterior norm proves agreement in every natural degree. *)
Lemma partial_exterior_isometric_chart_norm (R:realType) m n k q
    (D:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R k))
    (d:partial_function (R_n R n) (R_n R k)):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear D) ->
  (forall v w,partial_function_graph d v w <->exists x,D x=v /\ H x=w) ->
  is_partial_exterior_norm q d (euclidean_linear_jacobian q H).
Proof.
move=>hD hGraph.
have hNorm (v:'I_q->R_n R m):
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (e_lambda (fun i=>D (v i)) (ord_tuple q))=
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m)
      (e_lambda v (ord_tuple q)).
  rewrite -exterior_map_indexed_product.
  exact:(exterior_norm_orthogonal_natural (euclidean_two_nonzero R)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) hD).
constructor; first exact:euclidean_linear_jacobian_nonnegative.
- move=>v w hVW hUnit.
  have hex i:=(hGraph (v i) (w i)).1 (hVW i).
  have [x hx]:=choice hex.
  have hDX:(fun i=>D (x i))=v by apply:funext=>i; exact:(hx i).1.
  have hHX:(fun i=>H (x i))=w by apply:funext=>i; exact:(hx i).2.
  have hSource:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m)
      (e_lambda x (ord_tuple q))<=1.
    by rewrite -(hNorm x) hDX.
  rewrite -hHX -exterior_map_indexed_product.
  exact:(operator_norm_unit_bound (exterior_operator_normP (euclidean_two_nonzero R)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R k)
    (@coordinate_basisP R m) (hom_as_linear H) q) hSource).
- move=>J hJ hBound; apply:(exterior_unit_word_operator_bound
    (@coordinate_basisP R m) hJ)=>v hUnit.
  apply:(hBound (fun i=>D (v i)) (fun i=>H (v i)) _ _).
  + move=>i; apply:(hGraph _ _).2; exists (v i); by split.
  + by rewrite hNorm.
Qed.
