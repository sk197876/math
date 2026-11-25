(** Federer (1969), 2.7.16, printed p. 139, example (6): "Since the
    orthogonal group O(n) is a compact subset of Hom(R^n, R^n), there exists
    a unique left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1. For every transitive action A of O(n) on a
    homogeneous space X, and each x in X, the measure (A^x)_# theta_n over X
    is invariant with [(A^x)_# theta_n] X = 1." Here V is a space with an
    inner product B and a finite basis b (V = R^n gives O(n)), and the
    orthogonal group O(V) is the compact subgroup orthogonal_group of the
    linear group of V (OrthogonalGroupTopology.v), with any restricted group
    structure (is_subgroup_restriction). The module records how the members
    g of O(V) act as maps of V (orthogonal_element_map g is g as a member of
    Hom(V, V)), constructs a member of O(V) from every orthogonal linear map
    of V, and derives the two printed assertions from the general results
    for compact groups (CompactGroupHaarNormalisation.v,
    CompactGroupHomogeneousMeasures.v). The local erratum has no entry for
    p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric LinearBasis TensorUP Hom HomInner
  OrthogonalMaps IsotropyGroupTopology TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP
  MeasurePushforward HaarIntegralUP HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology CompactGroupHaarNormalisation CompactGroupHomogeneousMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OrthogonalElements.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation O := (orthogonal_group hB hb).

(** Source for [orthogonal_element_map]: a member g of the orthogonal
    group O(n), Federer 2.7.16, p. 139, as a member of Hom(R^n, R^n),
    the space of which O(n) is a subset. Definition: the inclusions of
    O(V) into the linear group of V and of the latter into Hom(V, V). *)
Definition orthogonal_element_map (g : O) : Hom V V := set_val (set_val g).

(** Source for [orthogonal_element_orthogonal]: each g in O(n) is an
    orthogonal map, Federer 1.7.2, p. 28, and 2.7.16, p. 139.
    Supporting lemma. *)
Lemma orthogonal_element_orthogonal (g : O) :
  is_orthogonal_map B B (hom_as_linear (orthogonal_element_map g)).
Proof. exact: (set_valP g). Qed.

(** Source for [orthogonal_element_inner]: g(x) . g(y) = x . y for g in
    O(n), Federer 1.7.2, p. 28. Supporting lemma. *)
Lemma orthogonal_element_inner (g : O) x y :
  B (orthogonal_element_map g x) (orthogonal_element_map g y) = B x y.
Proof. exact: (orthogonal_element_orthogonal g x y). Qed.

(** Source for [orthogonal_element_continuous]: the inclusion of O(n)
    into Hom(R^n, R^n) is continuous, Federer 2.7.16, p. 139, for the
    relative topology. Supporting lemma. *)
Lemma orthogonal_element_continuous : continuous (fun g : O => (orthogonal_element_map g : H)).
Proof.
move=> g; apply: (@continuous_comp O (set_type (linear_group hB hb)) H set_val set_val).
  exact: set_type_val_continuous.
exact: set_type_val_continuous.
Qed.

(** Source for [orthogonal_element_of]: every orthogonal linear map f of
    V is a member of O(V), Federer 1.7.2, p. 28, and 2.7.16, p. 139.
    Definition of the member with underlying map f. *)
Definition orthogonal_element_of (f : {linear V -> V}) (hf : is_orthogonal_map B B f) : O :=
  exist _ (exist _ (hom_of_linear f : H)
    (mem_set (orthogonal_map_injective hB hB (f := hom_as_linear (hom_of_linear f)) hf)))
    (mem_set (hf : orthogonal_maps hB hb (set_val (exist _ (hom_of_linear f : H)
      (mem_set (orthogonal_map_injective hB hB (f := hom_as_linear (hom_of_linear f)) hf)))))).

(** Source for [orthogonal_element_ofE]: the member of O(V) defined by
    an orthogonal linear map f acts as f, Federer 2.7.16, p. 139.
    Supporting lemma. *)
Lemma orthogonal_element_ofE (f : {linear V -> V}) (hf : is_orthogonal_map B B f) x :
  orthogonal_element_map (orthogonal_element_of hf) x = f x.
Proof. by []. Qed.

Variables (mulS : O -> O -> O) (invS : O -> O) (eS : O).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) O mulS invS eS.

(** Source for [orthogonal_element_mul]: the multiplication of O(n) is
    composition, g h = g o h, Federer 2.7.16, pp. 134 and 139.
    Supporting lemma. *)
Lemma orthogonal_element_mul (g h : O) :
  orthogonal_element_map (mulS g h) = hom_comp (orthogonal_element_map g) (orthogonal_element_map h).
Proof.
rewrite /orthogonal_element_map (subgroup_restriction_mul hS).
exact: (linear_group_mulE (linear_group_operations hB hb)).
Qed.

(** Source for [orthogonal_element_mulE]: (g h)(x) = g(h(x)) for g, h
    in O(n), Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_element_mulE (g h : O) x :
  orthogonal_element_map (mulS g h) x = orthogonal_element_map g (orthogonal_element_map h x).
Proof. by rewrite orthogonal_element_mul hom_compE. Qed.

(** Source for [orthogonal_element_unit]: the identity of O(n) is 1_V,
    Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_element_unit x : orthogonal_element_map eS x = x.
Proof.
rewrite /orthogonal_element_map (subgroup_restriction_unit hS).
by rewrite (linear_group_unitE (linear_group_operations hB hb)).
Qed.

(** Source for [orthogonal_element_inv]: g^{-1}(g(x)) = x and
    g(g^{-1}(x)) = x for g in O(n), Federer 2.7.16, p. 139. Supporting
    lemma. *)
Lemma orthogonal_element_inv (g : O) :
  cancel (orthogonal_element_map g) (orthogonal_element_map (invS g)) /\
  cancel (orthogonal_element_map (invS g)) (orthogonal_element_map g).
Proof.
rewrite /orthogonal_element_map (subgroup_restriction_inv hS).
exact: (linear_group_inv_cancel (linear_group_operations hB hb)).
Qed.

(** Source for [orthogonal_element_ext]: a member of O(n) is determined
    by its action on V, Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_element_ext (g h : O) :
  (forall x, orthogonal_element_map g x = orthogonal_element_map h x) -> g = h.
Proof. by move=> he; apply: val_inj; apply: val_inj; apply: hom_ext. Qed.

(** Source for [orthogonal_group_unique_haar_measure]: "Since the
    orthogonal group O(n) is a compact subset of Hom(R^n, R^n), there
    exists a unique left and right Haar measure theta_n over O(n) such
    that theta_n[O(n)] = 1", Federer 2.7.16, p. 139. Direct
    formalisation for O(V), by compact_group_unique_haar_measure and
    orthogonal_maps_compact. *)
Theorem orthogonal_group_unique_haar_measure :
  exists theta : set O -> \bar R,
    [/\ is_left_haar_measure mulS theta, is_right_haar_measure mulS invS theta,
      theta [set: O] = 1%E &
      forall psi, is_left_haar_measure mulS psi \/ is_right_haar_measure mulS invS psi ->
        psi [set: O] = 1%E -> psi = theta].
Proof.
exact: (compact_group_unique_haar_measure R (orthogonal_group_lch hS)
  (@orthogonal_group_compact_space R V B hB n b hb)).
Qed.

(** Source for [orthogonal_normalised_haar_measure_exists]: the measure
    theta_n of Federer 2.7.16, p. 139, exists: a left Haar measure of
    O(V) with total measure 1. Restatement of the existence part through
    is_normalised_haar_measure, the form used later. *)
Theorem orthogonal_normalised_haar_measure_exists :
  exists theta : set O -> \bar R, is_normalised_haar_measure mulS theta.
Proof.
exact: (normalised_haar_measure_exists R (orthogonal_group_lch hS)
  (@orthogonal_group_compact_space R V B hB n b hb)).
Qed.

(** Source for [orthogonal_normalised_haar_measure_unique]: the
    uniqueness of theta_n, Federer 2.7.16, p. 139: two normalised Haar
    measures of O(V) coincide. Restatement through
    is_normalised_haar_measure. *)
Theorem orthogonal_normalised_haar_measure_unique (theta psi : set O -> \bar R) :
  is_normalised_haar_measure mulS theta -> is_normalised_haar_measure mulS psi -> theta = psi.
Proof.
move=> [h1 e1] [h2 e2].
exact: (normalised_haar_measure_unique (orthogonal_group_lch hS)
  (@orthogonal_group_compact_space R V B hB n b hb) (or_introl h1) (or_introl h2) e1 e2).
Qed.

(** Source for [orthogonal_normalised_haar_measure_right]: theta_n is a
    right Haar measure, "left and right Haar measure", Federer 2.7.16,
    p. 139. Supporting lemma. *)
Lemma orthogonal_normalised_haar_measure_right (theta : set O -> \bar R) :
  is_normalised_haar_measure mulS theta -> is_right_haar_measure mulS invS theta.
Proof.
exact: (normalised_haar_measure_right (orthogonal_group_lch hS)
  (@orthogonal_group_compact_space R V B hB n b hb)).
Qed.

(** Source for [orthogonal_orbit_invariant_measure]: "For every
    transitive action A of O(n) on a homogeneous space X, and each x in
    X, the measure (A^x)_# theta_n over X is invariant with
    [(A^x)_# theta_n] X = 1", Federer 2.7.16, p. 139. Direct
    formalisation for O(V); of the standing hypotheses on X only the
    Hausdorff property is assumed. *)
Theorem orthogonal_orbit_invariant_measure (X : topologicalType) (A : O -> X -> X)
    (theta : set O -> \bar R) (x : X) :
  is_homogeneous_space mulS A -> hausdorff_space X -> is_normalised_haar_measure mulS theta ->
  is_normalised_invariant_measure A (measure_pushforward (orbit_map A x) theta).
Proof.
move=> hA hX htheta.
exact: (compact_orbit_pushforward_invariant (orthogonal_group_lch hS)
  (@orthogonal_group_compact_space R V B hB n b hb) hA hX x htheta).
Qed.

End OrthogonalElements.

Arguments orthogonal_element_map {R V B hB n b hb} g.
Arguments orthogonal_element_of {R V B} hB {n b} hb {f} hf.
