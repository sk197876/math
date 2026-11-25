(** Federer (1969), 2.6.6, p. 120: X_a, p_a, and the induced monomorphism of
    K(X_a) into K(X). A finite coordinate set is represented by its subtype,
    without choosing an enumeration. A section freezes coordinates outside a
    at a supplied product point. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot choice all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground ProductCylinderLattice DependentProductContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section Projection.
Variables (I : choiceType) (Y : I -> topologicalType).
Local Notation X := (prod_topology Y).

(** Source for [finite_coordinate_space]: X_a in Federer 2.6.6,
    p. 120, the product indexed by members of the finite set a. *)
Definition finite_coordinate_space (F : {fset I}) : topologicalType :=
  [the topologicalType of prod_topology (fun i : {i : I | i \in F} => Y (val i))].

(** Source for [finite_coordinate_projection]: p_a in Federer 2.6.6,
    p. 120, the coordinate restriction map. *)
Definition finite_coordinate_projection (F : {fset I}) (x : X) : finite_coordinate_space F :=
  fun i=>x (val i).

(** Source for [finite_coordinate_section]: supporting section of p_a
    for the monomorphism in Federer 2.6.6, p. 120. *)
Definition finite_coordinate_section (x0 : X) (F : {fset I})
    (u : finite_coordinate_space F) : X :=
  fun i=> if pselect (i \in F) is left h then u (Sub i h) else x0 i.

(** Source for [finite_coordinate_projection_continuous]: continuity
    of p_a, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_projection_continuous (F : {fset I}) :
  continuous (finite_coordinate_projection (F:=F)).
Proof. apply: dependent_product_map_continuous=> i; exact: proj_continuous. Qed.

(** Source for [finite_coordinate_section_continuous]: continuity of
    the section, supporting the characterization of L_a in Federer
    2.6.6, p. 120. *)
Lemma finite_coordinate_section_continuous (x0 : X) (F : {fset I}) :
  continuous (finite_coordinate_section x0 (F:=F)).
Proof.
apply: dependent_product_map_continuous=> i; rewrite /finite_coordinate_section.
case: pselect=> hi.
- exact (@proj_continuous [the choiceType of {j : I | j \in F}] (fun j=>Y (val j)) (Sub i hi)).
- exact: cst_continuous.
Qed.

(** Source for [finite_coordinate_section_projection]: p_a is onto
    when the full product has a point; this proves injectivity of
    pullback in Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_section_projection (x0 : X) (F : {fset I})
    (u : finite_coordinate_space F) :
  finite_coordinate_projection (F:=F) (finite_coordinate_section x0 u)=u.
Proof.
apply: functional_extensionality_dep=> i; case: i=> j hj.
rewrite /finite_coordinate_projection /finite_coordinate_section /=.
case: pselect=> h; last by move: h; rewrite hj.
by have -> : h=hj := bool_irrelevance h hj.
Qed.

(** Source for [finite_coordinate_pullback_injective]: the
    monomorphism assertion for p_a in Federer 2.6.6, p. 120,
    at the level of literal functions, independent of continuity. *)
Lemma finite_coordinate_pullback_injective (T : Type) (x0 : X) (F : {fset I})
    (f g : finite_coordinate_space F -> T) :
  f \o finite_coordinate_projection (F:=F)=g \o finite_coordinate_projection (F:=F) -> f=g.
Proof.
move=> he; apply: funext=> u.
have hh := congr1 (fun h=>h (finite_coordinate_section x0 u)) he.
by rewrite /= finite_coordinate_section_projection in hh.
Qed.
End Projection.

(** Source for [coordinate_determined_factorization]: equivalence
    between finite-coordinate dependence and a pullback from X_a,
    as used to define L_a in Federer 2.6.6, p. 120. *)
Lemma coordinate_determined_factorization (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y) (F : {fset I})
    (f : prod_topology Y -> R) :
  is_coordinate_determined F f ->
  f=(f \o finite_coordinate_section x0 (F:=F)) \o finite_coordinate_projection (F:=F).
Proof.
move=> hf; apply: funext=> x; apply: hf=> i hi.
rewrite /finite_coordinate_section /finite_coordinate_projection /=.
case: pselect=> h; first by [].
exfalso; exact: h hi.
Qed.
