(** Federer (1969), 3.2.10, p. 248: supporting continuous
    target-degree Jacobian calculation. This rectangular adjoint
    adapter uses only the sealed adjoint laws of 1.7.4,
    p. 30, and finite-dimensional norm equivalence. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm AdjointUP Adjoint AdjointLaws
  HomSpaceNormTopology EuclideanHomOperator NormMetric NormDifferentialUP
  NormFiniteLinearBound NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_rectangular_adjoint]: the adjoint
    used in the normal Jacobian of Federer 3.2.10, p. 248,
    specified and sealed already in 1.7.4, p. 30. This
    is a type adapter, not a new chosen construction. *)
Definition euclidean_rectangular_adjoint (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)):Hom (R_n R n) (R_n R m):=
  hom_of_linear (@inner_adjoint R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear L)).

(** Source for [euclidean_rectangular_adjoint_pairing]: supporting
    adjoint pairing in Federer 3.2.10, p. 248, directly
    from the defining identity of 1.7.4, p. 30. *)
Lemma euclidean_rectangular_adjoint_pairing (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) x y:
  euclidean_inner_product x (euclidean_rectangular_adjoint L y)=
    euclidean_inner_product (L x) y.
Proof. exact:inner_adjointP. Qed.

(** Source for [euclidean_rectangular_adjoint_linear]: supporting
    dependence on the differential in Federer 3.2.10,
    p. 248. Linearity follows from the adjoint laws of
    1.7.4, p. 30, without unfolding its witness. *)
Lemma euclidean_rectangular_adjoint_linear (R:realType) m n:
  linear (@euclidean_rectangular_adjoint R m n).
Proof.
move=>c L M; apply:hom_ext=>y.
apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
rewrite (euclidean_rectangular_adjoint_pairing (c*:L+M))
  (bilDr (inner_bilinear (@euclidean_inner_productP R m)))
  (bilZr (inner_bilinear (@euclidean_inner_productP R m)))
  !euclidean_rectangular_adjoint_pairing.
change (euclidean_inner_product (c*:L x+M x) y=
  c*euclidean_inner_product (L x) y+euclidean_inner_product (M x) y).
by rewrite (bilDl (inner_bilinear (@euclidean_inner_productP R n)))
  (bilZl (inner_bilinear (@euclidean_inner_productP R n))).
Qed.
HB.instance Definition _ (R:realType) m n:=GRing.isLinear.Build R
  (Hom (R_n R m) (R_n R n)) (Hom (R_n R n) (R_n R m))
  *:%R (@euclidean_rectangular_adjoint R m n)
  (@euclidean_rectangular_adjoint_linear R m n).

(** Source for [euclidean_rectangular_adjoint_continuous]: supporting
    measurability in Federer 3.2.10, p. 248. The adjoint
    is continuous for the source and target operator norms,
    using only finite-dimensional boundedness from 1.7.1, p. 28. *)
Lemma euclidean_rectangular_adjoint_continuous (R:realType) m n:
  continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_rectangular_adjoint L:
      real_norm_metric_space (@euclidean_operator_norm_is_norm R n m))).
Proof.
pose NX:=@euclidean_operator_norm R m n.
pose NY:=@euclidean_operator_norm R n m.
pose hNX:=@euclidean_operator_norm_is_norm R m n.
pose hNY:=@euclidean_operator_norm_is_norm R n m.
have [q [b hb]]:=@hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
pose A:=hom_of_linear (GRing.Linear.clone _ _ _ _ (@euclidean_rectangular_adjoint R m n) _).
have hBound:norm_bounded_linear NX NY A:=norm_finite_linear_bounded hNX hNY hb A.
exact (@norm_bounded_linear_continuous R (Hom (R_n R m) (R_n R n))
  (Hom (R_n R n) (R_n R m)) NX NY hNX hNY A hBound).
Qed.
