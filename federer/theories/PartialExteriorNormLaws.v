(** Federer (1969), 3.2.20, p. 256: consequences of the
    intrinsic partial exterior-norm laws. Uniqueness uses only leastness;
    ambient linear maps supply bounds, not off-domain definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps FiniteExteriorPowers
  PartialFunctionUP InnerNorm InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorNorm ExteriorMaps
  ExteriorOperatorEstimate ExteriorOperatorNorm OperatorNormUP EuclideanLinearJacobian
  OrthonormalFamilies PartialExteriorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partial_exterior_norm_unique]: supporting well-definedness
    of the norm in Federer 3.2.20, p. 256. Its independent
    least-bound laws determine one real value on the actual partial graph. *)
Lemma partial_exterior_norm_unique (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k)) (J L : R) :
  is_partial_exterior_norm q d J -> is_partial_exterior_norm q d L -> J=L.
Proof.
move=> hJ hL; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (partial_exterior_norm_least hJ (partial_exterior_norm_nonnegative hL) (partial_exterior_norm_bound hL)).
- exact: (partial_exterior_norm_least hL (partial_exterior_norm_nonnegative hJ) (partial_exterior_norm_bound hJ)).
Qed.

(** Source for [partial_exterior_representative_bound]: supporting finite
    bound for the supremum in Federer 3.2.20, p. 256,
    from the ambient exterior operator norm of 1.7.6, pp. 33–34.
    Only agreement on actual partial-graph values is used. *)
Lemma partial_exterior_representative_bound (R : realType) n k q
    (d : partial_function (R_n R n) (R_n R k)) (D : Hom (R_n R n) (R_n R k)) :
  (forall v w, partial_function_graph d v w -> D v=w) ->
  is_partial_exterior_bound q d (euclidean_linear_jacobian q D).
Proof.
move=> hModel v w hGraph hUnit.
have hFamily : (fun i=>D (v i))=w.
  apply: funext=> i; exact: hModel _ _ (hGraph i).
have hWord : exterior_power_map (hom_as_linear D) q (e_lambda v (ord_tuple q))=
    e_lambda w (ord_tuple q).
  by rewrite exterior_map_indexed_product hFamily.
have hOp := @exterior_operator_normP R (euclidean_two_nonzero R)
  (R_n R n) (R_n R k) (@euclidean_inner_product R n) (@euclidean_inner_product R k)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R k)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (hom_as_linear D) q.
have hBound := operator_norm_unit_bound hOp hUnit.
by rewrite hWord in hBound.
Qed.

(** Source for [empty_exterior_word_unit_norm]: the empty product
    convention of 1.3.1 and 1.7.5, p. 32, in the degree-zero
    boundary of Federer 3.2.20, p. 256. *)
Lemma empty_exterior_word_unit_norm (R : realType) n (v : 'I_0 -> R_n R n) :
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda v (ord_tuple 0))= 1.
Proof.
have hEmpty : orthonormal_family (@euclidean_inner_product R n) v.
  by move=> i; have := ltn_ord i; rewrite ltn0.
exact: (orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) hEmpty).
Qed.

(** Source for [partial_exterior_norm_zero_degree]: degree zero in
    the norm formula of Federer 3.2.20, p. 256. The value
    is one for every partial graph, while the approximate Jacobian's
    own domain still requires actual approximate differentiability. *)
Lemma partial_exterior_norm_zero_degree (R : realType) n k
    (d : partial_function (R_n R n) (R_n R k)) : is_partial_exterior_norm 0 d 1.
Proof.
constructor; first exact: ler01.
- by move=> v w _ _; rewrite empty_exterior_word_unit_norm.
- move=> L hL hBound.
  have hGraph : forall i : 'I_0, partial_function_graph d (0 : R_n R n) (0 : R_n R k).
    by move=> i; have := ltn_ord i; rewrite ltn0.
  have hUnit : exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (e_lambda (fun _ : 'I_0=>(0 : R_n R n)) (ord_tuple 0))<=1.
    by rewrite empty_exterior_word_unit_norm.
  have hh := hBound (fun _ : 'I_0=>(0 : R_n R n)) (fun _ : 'I_0=>(0 : R_n R k)) hGraph hUnit.
  by rewrite empty_exterior_word_unit_norm in hh.
Qed.
