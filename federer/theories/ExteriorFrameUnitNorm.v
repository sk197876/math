(** Federer (1969), 1.7.7, p. 34: both exterior maps in the proof have
    operator norm one. The degree is the dimension of the frame space R^m,
    so its unit top vector exists even for m=0. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm OrthogonalMaps AdjointUP
  ExteriorGrading ExteriorMaps ExteriorAdjointConsequences
  InnerExterior InnerExteriorPositivity ExteriorNorm ProjectionNorm
  ExteriorProjectionNorm OperatorNormUP GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates CoordinateProjection FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_product_unit_norm]: Federer 1.7.7,
    p. 34, supporting unit witness for the top exterior power
    of the frame source, including the empty product in R^0. *)
Lemma euclidean_top_product_unit_norm (R : rcfType)
    (h2 : (1+1 : R) != 0) m :
  exterior_norm h2 (@euclidean_inner_productP R m)
    (e_lambda (@coordinate_basis R m) (ord_tuple m)) = 1.
Proof.
apply: orthonormal_product_unit_norm => i j.
by rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
Qed.

(** Source for [exterior_frame_operator_norm_one]: Federer 1.7.7,
    p. 34, the m-th exterior map of an orthogonal injection
    from R^m has operator norm one, including m=0. *)
Theorem exterior_frame_operator_norm_one (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (f : {linear R_n R m -> V})
    (hf : is_orthogonal_map (@euclidean_inner_product R m) B f) :
  is_operator_norm
    (exterior_inner_productP h2 (@euclidean_inner_productP R m) m)
    (exterior_inner_productP h2 hB m) (exterior_power_map f m) 1.
Proof.
constructor.
- move=> x hx.
  change (exterior_norm h2 hB (exterior_power_map f m x) <= 1).
  by rewrite (exterior_orthogonal_norm h2 (@euclidean_inner_productP R m) hB hf).
- exists (e_lambda (@coordinate_basis R m) (ord_tuple m)).
  change (exterior_norm h2 (@euclidean_inner_productP R m)
      (e_lambda (@coordinate_basis R m) (ord_tuple m)) <= 1 /\
    exterior_norm h2 hB (exterior_power_map f m
      (e_lambda (@coordinate_basis R m) (ord_tuple m))) = 1).
  rewrite (exterior_orthogonal_norm h2 (@euclidean_inner_productP R m) hB hf)
    euclidean_top_product_unit_norm; by split.
Qed.

(** Source for [exterior_projection_operator_norm_one]: Federer
    1.7.7, p. 34, the m-th exterior map of an orthogonal
    projection onto R^m has operator norm one, including m=0. *)
Theorem exterior_projection_operator_norm_one (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (p : {linear V -> R_n R m})
    (hp : is_orthogonal_projection B (@euclidean_inner_product R m) p) :
  is_operator_norm (exterior_inner_productP h2 hB m)
    (exterior_inner_productP h2 (@euclidean_inner_productP R m) m)
    (exterior_power_map p m) 1.
Proof.
exact: (@orthogonal_projection_unit_norm R _ _ _ _
  (exterior_inner_productP h2 hB m)
  (exterior_inner_productP h2 (@euclidean_inner_productP R m) m)
  (exterior_power_map p m)
  (exterior_power_orthogonal_projection h2 hB (@euclidean_inner_productP R m) hp m)
  (e_lambda (@coordinate_basis R m) (ord_tuple m))
  (euclidean_top_product_unit_norm h2 m)).
Qed.
