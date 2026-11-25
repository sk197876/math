(** Federer (1969), 1.7.7, p. 34: the exterior map of an orthogonal
    projection contracts lengths; in top target degree its norm is one. The
    corresponding injection is an isometry. these are consequences of the
    1.7.6 orthogonality results. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP InnerProductUP InnerNorm OrthogonalMaps AdjointUP
  AdjointCriteria ExteriorAdjointConsequences ExteriorMapScaling ExteriorMaps
  ExteriorGrading InnerExterior InnerExteriorPositivity InnerExteriorNaturality ExteriorNorm
  ProjectionNorm OperatorNormUP EuclideanInnerProduct GrassmannAbbreviations
  FiniteCoordinates CoordinateProjection FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_projection_norm_bound]: Federer 1.7.7,
    p. 34, first inequality in the proof, valid for every vector,
    without a simplicity or dimension hypothesis. *)
Theorem exterior_projection_norm_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (p : {linear V -> U}) (hp : is_orthogonal_projection B C p)
    m (x : exterior_power V m) :
  exterior_norm h2 hC (exterior_power_map p m x) <= exterior_norm h2 hB x.
Proof.
exact: (@orthogonal_projection_norm_bound R _ _ _ _
  (exterior_inner_productP h2 hB m) (exterior_inner_productP h2 hC m)
  (exterior_power_map p m) (exterior_power_orthogonal_projection h2 hB hC hp m) x).
Qed.

(** Source for [exterior_orthogonal_norm]: Federer 1.7.7,
    p. 34, the exterior map of an orthogonal injection preserves
    length. This stronger pointwise statement supplies its norm bound. *)
Theorem exterior_orthogonal_norm (R : rcfType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (hf : is_orthogonal_map B C f)
    m (x : exterior_power V m) :
  exterior_norm h2 hC (exterior_power_map f m x) = exterior_norm h2 hB x.
Proof.
apply: inner_norm_value; first exact: exterior_norm_nonnegative.
rewrite exterior_norm_square.
symmetry; exact: (@exterior_inner_orthogonal_natural R h2 V U B C hB hC f hf m x x).
Qed.

(** Source for [exterior_adjoint_retraction]: Federer 1.7.7,
    p. 34, the exterior maps of an orthogonal injection and its
    adjoint cancel on the source exterior power. *)
Theorem exterior_adjoint_retraction (R : realFieldType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (f : {linear V -> U})
    (a : {linear U -> V}) (ha : is_adjoint B C f a)
    (hf : is_orthogonal_map B C f) m :
  cancel (exterior_power_map f m) (exterior_power_map a m).
Proof.
have hk := proj1 (orthogonal_iff_adjoint_left_inverse hB ha) hf.
move=> x; rewrite exterior_power_map_composition.
have he := @exterior_power_map_ext R V V (linear_comp a f) (linear_id V) hk m x.
by rewrite exterior_power_map_identity in he.
Qed.
