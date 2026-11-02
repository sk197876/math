(** Federer (1969), 2.6.6, p. 120: finite-coordinate continuous functions
    form the uniformly dense union L. This file proves density by freezing
    the other coordinates at a chosen product point. It also treats finite
    and empty index sets. Source context and the limited supporting
    correspondence. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactProductFiniteControl DependentProductContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section Cylinders.
Variables (I : choiceType) (Y : I -> topologicalType).
Local Notation X := (prod_topology Y).

(** Source for [product_coordinate_freezing]: supporting retraction onto
    a finite-coordinate slice for density in Federer 2.6.6, p. 120.
    Coordinates outside F are fixed at x0; this construction is used
    only to exhibit approximating continuous functions. *)
Definition product_coordinate_freezing (x0 : X) (F : {fset I}) (x : X) : X :=
  fun i => if i \in F then x i else x0 i.

(** Source for [product_coordinate_freezing_continuous]: supporting
    continuity of the finite-coordinate retraction, Federer 2.6.6,
    p. 120, from the defining product topology. *)
Lemma product_coordinate_freezing_continuous (x0 : X) (F : {fset I}) :
  continuous (product_coordinate_freezing x0 F).
Proof.
apply: dependent_product_map_continuous=> i.
case: (boolP (i \in F))=> hi.
- have he : (fun x : X=>product_coordinate_freezing x0 F x i)=(fun x : X=>x i).
    by apply: funext=> x; rewrite /product_coordinate_freezing hi.
  rewrite he; exact: proj_continuous.
- have he : (fun x : X=>product_coordinate_freezing x0 F x i)=(fun _ : X=>x0 i).
    by apply: funext=> x; rewrite /product_coordinate_freezing (negbTE hi).
  rewrite he; exact: cst_continuous.
Qed.

(** Source for [product_coordinate_freezing_agreement]: the retraction
    preserves the selected coordinates, supporting Federer 2.6.6,
    p. 120, density of finite-coordinate functions. *)
Lemma product_coordinate_freezing_agreement (x0 x : X) (F : {fset I}) i :
  i \in F -> product_coordinate_freezing x0 F x i=x i.
Proof. by move=> hi; rewrite /product_coordinate_freezing hi. Qed.

(** Source for [product_coordinate_freezing_determined]: supporting
    finite-coordinate dependence in Federer 2.6.6, p. 120. *)
Lemma product_coordinate_freezing_determined (x0 x y : X) (F : {fset I}) :
  (forall i, i \in F -> x i=y i) ->
  product_coordinate_freezing x0 F x=product_coordinate_freezing x0 F y.
Proof.
move=> h; apply: functional_extensionality_dep=> i.
by rewrite /product_coordinate_freezing; case: ifP=> hi; [rewrite h|].
Qed.
End Cylinders.

(** Source for [compact_product_cylinder_approximation]: the uniform
    density assertion for L in K(X), Federer 2.6.6, p. 120,
    in its equivalent form using continuous functions determined by
    finitely many coordinates. A product point is supplied here;
    normalization of the factor integrals supplies nonemptiness in the
    application. No countability assumption on the index set is made. *)
Theorem compact_product_cylinder_approximation (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y)
    (f : prod_topology Y -> real_line_metric R) (e : R) :
  compact [set: prod_topology Y] -> continuous f -> 0<e ->
  exists (F : {fset I}) (g : prod_topology Y -> real_line_metric R),
    continuous g /\ (forall x y, (forall i, i \in F -> x i=y i) -> g x=g y) /\
    forall x, `|f x-g x|<e.
Proof.
move=> hX hf he.
have [F hF] := @compact_product_continuous_finite_control R I Y f e hX hf he.
exists F, (f \o product_coordinate_freezing x0 F); split.
- move=> x; exact: continuous_comp (@product_coordinate_freezing_continuous I Y x0 F x) (hf _).
split.
- move=> x y h; congr f; exact: product_coordinate_freezing_determined h.
- move=> x; apply: hF=> i hi; symmetry; exact: product_coordinate_freezing_agreement hi.
Qed.
