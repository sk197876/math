(** Federer (1969), 3.2.10, p. 248: supporting
    evaluation of the complementary Jacobian on the ordered
    coordinate volume, by 1.7.6, p. 34. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian ExteriorGrading ExteriorMaps ExteriorMapScaling
  ExteriorOperatorNorm TopExteriorNorm ExteriorFrameUnitNorm FiniteExteriorPowers
  ExteriorHomogeneousProducts ExteriorNorm ExteriorNormNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_frame_jacobian]: the complementary
    exterior-map norm in Federer 3.2.10, p. 248,
    evaluated using the unit top source product of 1.7.6,
    p. 34. No orthogonality of j is needed for this
    supporting evaluation formula, and k=0 is included. *)
Lemma euclidean_frame_jacobian (R:realType) m n k
    (M:Hom (R_n R m) (R_n R n)) (j:{linear R_n R k->R_n R m}):
  euclidean_linear_jacobian k (hom_comp M (hom_of_linear j))=
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (exterior_power_map (hom_as_linear M) k
        (exterior_power_map j k (e_lambda (@coordinate_basis R k) (ord_tuple k)))).
Proof.
rewrite /euclidean_linear_jacobian.
rewrite (@top_exterior_operator_unit_value R (euclidean_two_nonzero R)
  (R_n R k) (R_n R n) (@euclidean_inner_product R k) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R k) (@euclidean_inner_productP R n) k
  (@coordinate_basis R k) (@coordinate_basisP R k)
  (hom_as_linear (hom_comp M (hom_of_linear j)))
  (e_lambda (@coordinate_basis R k) (ord_tuple k))
  (euclidean_top_product_unit_norm (euclidean_two_nonzero R) k)).
have hComp:hom_as_linear (hom_comp M (hom_of_linear j))=1 linear_comp (hom_as_linear M) j
  by move=>x.
by rewrite (exterior_power_map_ext hComp _) -exterior_power_map_composition.
Qed.

(** Source for [exterior_map_reindex_degree]: Federer 3.2.10,
    p. 248, supporting degree bookkeeping in the complementary
    volume. Transport along equal degrees commutes with the
    exterior map; no vector or map is changed. *)
Lemma exterior_map_reindex_degree (R:fieldType) (V W:lmodType R)
    (f:{linear V->W}) m n (h:m=n) (x:exterior_power V m):
  exterior_reindex h (exterior_power_map f m x)=
    exterior_power_map f n (exterior_reindex h x).
Proof. by case:n /h. Qed.
