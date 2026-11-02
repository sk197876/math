(** Supporting the last identity of Federer (1969), 2.10.16, p. 178: compose
    p in O*(n,k) with q in O*(k,m). Specify the operation by its evaluation
    law, prove its continuity from continuous Hom composition, and prove
    existence using 1.7.4, pp. 30–31. Downstream proofs use only the law,
    not a chosen representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric Hom HomInner TensorUP ProjectionCriteria OrthogonalInjectionSpaces
  IsotropyGroupTopology EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace
  EuclideanProjectionMetric TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_projection_composition]: supporting
    abstract evaluation law for 2.10.16, p. 178: the
    projection C(q,p) takes x to q(p(x)). *)
Definition is_euclidean_projection_composition (R : realType) (n k m : nat)
    (C : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k ->
      orthogonal_projection_metric_space R n m) :=
  forall q p x, euclidean_projection_linear (C (q,p)) x=
    euclidean_projection_linear q (euclidean_projection_linear p x).

(** Source for [euclidean_projection_composition_continuous]:
    supporting parameter continuity for 2.10.16, p. 178.
    The evaluation law identifies C with ordinary continuous
    Hom composition in the inherited relative topology. *)
Lemma euclidean_projection_composition_continuous (R : realType) (n k m : nat)
    (C : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k ->
      orthogonal_projection_metric_space R n m) :
  is_euclidean_projection_composition C -> continuous C.
Proof.
move=> hC.
pose Q := euclidean_projection_space R k m.
pose P := euclidean_projection_space R n k.
pose H a b : metricType R := [the metricType R of inner_metric_space
  (hom_inner_productP (@euclidean_inner_productP R a)
    (@euclidean_inner_productP R b) (@coordinate_basisP R a))].
change (continuous (C : Q*P -> euclidean_projection_space R n m)).
apply (@set_type_continuous_into (H n m) (euclidean_orthogonal_projections R n m) (Q*P)%type C).
have he : set_val \o C=(fun z : H k m * H n k =>
    (hom_comp (z.1 : Hom (R_n R k) (R_n R m)) (z.2 : Hom (R_n R n) (R_n R k)) : H n m)) \o
    (fun z : Q*P => ((set_val z.1 : H k m),(set_val z.2 : H n k))).
  apply/funext=> -[q p]; apply: hom_ext=> x.
  exact (hC q p x).
rewrite he.
have hf : continuous (fun z : Q*P => ((set_val z.1 : H k m),(set_val z.2 : H n k))).
  apply (@topological_pair_continuous (Q*P)%type (H k m) (H n k)
    (fun z : Q*P => (set_val z.1 : H k m)) (fun z : Q*P => (set_val z.2 : H n k))).
  - move=> z; exact: continuous_comp (@first_projection_continuous Q P z)
      (@set_type_val_continuous (H k m) (euclidean_orthogonal_projections R k m) z.1).
  - move=> z; exact: continuous_comp (@second_projection_continuous Q P z)
      (@set_type_val_continuous (H n k) (euclidean_orthogonal_projections R n k) z.2).
move=> z.
exact (@continuous_comp (Q*P)%type (H k m * H n k)%type (H n m)
  (fun z : Q*P => ((set_val z.1 : H k m),(set_val z.2 : H n k)))
  (fun z : H k m * H n k =>
    (hom_comp (z.1 : Hom (R_n R k) (R_n R m)) (z.2 : Hom (R_n R n) (R_n R k)) : H n m))
  z (hf z)
  (@hom_composition_continuous_general R (R_n R n) (R_n R k) (R_n R m)
    (@euclidean_inner_product R n) (@euclidean_inner_product R k) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R n) (@euclidean_inner_productP R k) (@euclidean_inner_productP R m)
    n (@coordinate_basis R n) k (@coordinate_basis R k)
    (@coordinate_basisP R n) (@coordinate_basisP R k) (set_val z.1,set_val z.2))).
Qed.

(** Source for [euclidean_projection_composition_exists]: proved
    existence supporting 2.10.16, p. 178. The composition
    of the orthogonal adjoints is an orthogonal injection by
    1.7.4, pp. 30–31. No unproved operation is introduced. *)
Theorem euclidean_projection_composition_exists (R : realType) (n k m : nat) :
  exists C, @is_euclidean_projection_composition R n k m C.
Proof.
have hex (z : orthogonal_projection_metric_space R k m * orthogonal_projection_metric_space R n k) :
    exists r : orthogonal_projection_metric_space R n m,
      forall x, euclidean_projection_linear r x=
        euclidean_projection_linear z.1 (euclidean_projection_linear z.2 x).
  pose f := linear_comp (euclidean_projection_linear z.1) (euclidean_projection_linear z.2).
  have hf := orthogonal_projection_composition
    (orthogonal_projection_map_projection z.2) (orthogonal_projection_map_projection z.1).
  exists (orthogonal_projection_of (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n) hf).
  by move=> x.
exists (fun z => projT1 (cid (hex z)))=> q p.
exact: projT2 (cid (hex (q,p))).
Qed.
