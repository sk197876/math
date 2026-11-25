(** Normal product coordinates supporting the compactness assertion in
    Federer (1969), 2.10.30, p. 195. The split map lands in the orthogonal
    hyperplane times the real line, viewed as a closed part of the ambient
    space times the line. This avoids choosing a basis for the compactness
    proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology OrthonormalFamilies
  InnerCoordinateContinuity RealMetricBackground UnitNormalGeometry UnitNormalTopology
  SteinerSymmetrisationUP ProductSections TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coordinates.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation E := (inner_metric_space hB).
Variable u : V.

(** Source for [normal_product_split]: supporting intrinsic split into
    hyperplane foot and scalar coordinate in 2.10.30, p. 195 *)
Definition normal_product_split (x : E) : E*real_line_metric R :=
  (normal_foot hB u x,inner_coordinate hB u x).

(** Source for [normal_product_join]: supporting intrinsic
    reassembly from normal-line coordinates in 2.10.30,
    p. 195. On the split image this is
    inverse to the split map. *)
Definition normal_product_join (z : E*real_line_metric R) : E := z.1+z.2*:u.

(** Source for [normal_product_split_continuous]: supporting
    continuous product-coordinate image for compactness
    in 2.10.30, p. 195. *)
Lemma normal_product_split_continuous : continuous normal_product_split.
Proof.
apply: topological_pair_continuous; first exact: normal_foot_continuous.
exact: inner_coordinate_continuous.
Qed.

(** Source for [normal_product_join_continuous]: supporting
    continuous return to the ambient space for the
    compactness conclusion of 2.10.30, p. 195. *)
Lemma normal_product_join_continuous : continuous normal_product_join.
Proof.
move=> z; apply: continuousD; first exact: first_projection_continuous.
apply: continuousZ; [exact: second_projection_continuous|exact: cst_continuous].
Qed.

(** Source for [normal_product_splitK]: supporting reconstruction from
    normal coordinates in 2.10.30, p. 195 *)
Lemma normal_product_splitK : cancel normal_product_split normal_product_join.
Proof. move=> x; exact (normal_decomposition hB u x). Qed.

(** Source for [normal_product_join_coordinates]: supporting
    normal-line coordinate identities for 2.10.30,
    p. 195. The first factor is restricted
    to the hyperplane, as in the book. *)
Lemma normal_product_join_coordinates y t :
  B u u= 1 -> inner_coordinate hB u y=0 ->
  normal_product_split (normal_product_join (y,t))=(y,t).
Proof.
move=> hu hy.
change ((normal_foot hB u (y+t*:u),inner_coordinate hB u (y+t*:u))=(y,t)).
by rewrite (@normal_line_foot R V B hB u hu y t hy)
  (@normal_line_coordinate R V B hB u hu y t hy).
Qed.

(** Source for [normal_product_image_section]: supporting scalar-section
    description of a split set in 2.10.30, p. 195 *)
Lemma normal_product_image_section (S : set E) y :
  B u u= 1 -> inner_coordinate hB u y=0 ->
  product_vertical_section (normal_product_split @` S) y=normal_scalar_section u S y.
Proof.
move=> hu hy; apply/seteqP; split=> t.
- move=> [x hx he].
  have hh := congr1 normal_product_join he; rewrite normal_product_splitK in hh.
  change (S (normal_product_join (y,t))); by rewrite -hh.
- move=> ht; exists (normal_product_join (y,t))=> //.
  exact (normal_product_join_coordinates t hu hy).
Qed.

(** Source for [normal_product_image_off_hyperplane]: supporting
    absence of extraneous normal fibres in 2.10.30,
    p. 195. The ambient product representation
    adds no points over feet outside the hyperplane. *)
Lemma normal_product_image_off_hyperplane (S : set E) y :
  B u u= 1 -> inner_coordinate hB u y<>0 ->
  product_vertical_section (normal_product_split @` S) y=set0.
Proof.
move=> hu hy; apply/seteqP; split=> t; last by case.
move=> [x hx he]; exfalso; apply: hy.
have hf := congr1 fst he.
change (normal_foot hB u x=y) in hf.
by rewrite -hf (normal_coordinate_foot hB hu x).
Qed.
End Coordinates.
