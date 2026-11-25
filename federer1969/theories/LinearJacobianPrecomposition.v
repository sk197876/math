(** Federer (1969), 3.2.2, p. 242: source linear coordinate
    changes multiply a top-source Jacobian by the absolute determinant.
    This follows directly from the top exterior map, 1.7.6, p. 33. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm EuclideanLinearMaps ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorDeterminant
  ExteriorNorm FiniteExteriorPowers ExteriorFrameUnitNorm ExteriorOperatorNorm TopExteriorNorm EuclideanLinearJacobian
  LinearJacobianSandwich.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_jacobian_precompose]: the determinant
    factor in Federer 3.2.2, p. 242, inherited from 1.7.6,
    p. 33. J_m(L composed with s)=|det s| J_m L for
    every source endomorphism, including singular s and degree zero. *)
Lemma euclidean_top_jacobian_precompose (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) (s:Hom (R_n R m) (R_n R m)) :
  euclidean_linear_jacobian m (hom_comp L s)=
    `|euclidean_det (hom_as_linear s)|*euclidean_linear_jacobian m L.
Proof.
pose w:=e_lambda (@coordinate_basis R m) (ord_tuple m).
have hw:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) w= 1.
  exact (euclidean_top_product_unit_norm (euclidean_two_nonzero R) m).
have hComp:hom_as_linear (hom_comp L s)=1 linear_comp (hom_as_linear L) (hom_as_linear s).
  by move=>v.
rewrite /euclidean_linear_jacobian.
rewrite (@top_exterior_operator_unit_value R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m
  (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear (hom_comp L s)) w hw).
rewrite (exterior_power_map_ext hComp w) -exterior_power_map_composition.
rewrite (@detE R (euclidean_two_nonzero R) m (R_n R m) (@coordinate_basis R m)
  (@coordinate_basisP R m) (hom_as_linear s) w) linearZ exterior_norm_scale.
congr (_*_).
symmetry; exact (@top_exterior_operator_unit_value R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m
  (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear L) w hw).
Qed.

(** Source for [euclidean_relative_jacobian_sandwich]: the Jacobian
    bounds implied by the first condition on Z(s,i), Federer
    3.2.2, p. 242. Pull the differential back through the
    actual source automorphism and apply the vector-to-Jacobian
    estimate, then restore the determinant factor. *)
Theorem euclidean_relative_jacobian_sandwich (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) (s t:Hom (R_n R m) (R_n R m)) c C :
  cancel s t -> cancel t s -> 0<=c -> 0<=C ->
  (forall v,c*inner_norm (@euclidean_inner_productP R m) (s v)<=inner_norm (@euclidean_inner_productP R n) (L v)) ->
  (forall v,inner_norm (@euclidean_inner_productP R n) (L v)<=C*inner_norm (@euclidean_inner_productP R m) (s v)) ->
  c^+m*`|euclidean_det (hom_as_linear s)|<=euclidean_linear_jacobian m L /\
  euclidean_linear_jacobian m L<=C^+m*`|euclidean_det (hom_as_linear s)|.
Proof.
move=>hst hts hc hC hLower hUpper.
pose F:=hom_comp L t.
have hl v:c*inner_norm (@euclidean_inner_productP R m) v<=inner_norm (@euclidean_inner_productP R n) (F v).
  by have hh:=hLower (t v); rewrite hts in hh.
have hu v:inner_norm (@euclidean_inner_productP R n) (F v)<=C*inner_norm (@euclidean_inner_productP R m) v.
  by have hh:=hUpper (t v); rewrite hts in hh.
have [hJlo hJhi]:=euclidean_top_jacobian_sandwich hc hC hl hu.
have he:hom_comp F s=L by apply:hom_ext=>v; change (L (t (s v))=L v); rewrite hst.
have hj:=euclidean_top_jacobian_precompose F s; rewrite he in hj.
have hComm : `|euclidean_det (hom_as_linear s)|*euclidean_linear_jacobian m F=
    euclidean_linear_jacobian m F*`|euclidean_det (hom_as_linear s)| :=mulrC _ _.
rewrite hj hComm; split.
- exact (ler_wpM2r (normr_ge0 _) hJlo).
- exact (ler_wpM2r (normr_ge0 _) hJhi).
Qed.
