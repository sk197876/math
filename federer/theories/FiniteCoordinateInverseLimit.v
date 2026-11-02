(** Federer (1969), 2.6.6, pp. 120–121: "We observe that in the preceding
    argument the passage from finite to infinite products depends only on
    the representation of X as inverse limit of the spaces X_a, and on the
    consistency conditions p^b_a#(mu_b) = mu_a." This file proves that
    representation: the finite sets of indices, ordered by inclusion, the
    spaces X_a and the projections p^b_a form a compact Hausdorff inverse
    system in the sense of [is_compact_inverse_system], and X with the
    projections p_a is its inverse limit in the sense of
    [is_compact_inverse_limit]. Bonding maps must be given for all pairs of
    indices; for a not contained in b the map u -> p_a(s(u)) uses a point x0
    of X to fill missing coordinates, and for a subset b it equals p^b_a. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinateProjection CompactInverseSystemUP CompactInverseLimitUP
  NormalizedProductSpace FiniteCoordinateSplit FiniteCoordinateAdjoinProduct FiniteCoordinateRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section FiniteInverseSystem.
Variables (I : choiceType) (Y : I -> topologicalType) (x0 : prod_topology Y).
Local Notation X := (prod_topology Y).

(** Source for [finite_coordinate_subset]: the directed order of the
    class A of finite subsets of J by inclusion, Federer 2.6.6,
    p. 120. *)
Definition finite_coordinate_subset (F G : {fset I}) : Prop := {subset F <= G}.

(** Source for [finite_coordinate_bonding]: bonding maps of the
    inverse system of the spaces X_a, Federer 2.6.6, pp. 120–121;
    for a subset b this is p^b_a. *)
Definition finite_coordinate_bonding (F G : {fset I}) (u : finite_coordinate_space Y G) :
    finite_coordinate_space Y F :=
  finite_coordinate_projection (F:=F) (finite_coordinate_section x0 u).

(** Source for [finite_coordinate_bonding_restriction]: for a subset b
    the bonding map is the projection p^b_a of Federer 2.6.6, p. 120;
    the point x0 is immaterial. *)
Lemma finite_coordinate_bonding_restriction (F G : {fset I}) (hFG : {subset F <= G})
    (u : finite_coordinate_space Y G) :
  @finite_coordinate_bonding F G u=finite_coordinate_restriction hFG u.
Proof.
apply: functional_extensionality_dep=> -[j hj].
rewrite /finite_coordinate_bonding /finite_coordinate_projection /finite_coordinate_restriction /=.
exact: finite_coordinate_section_member.
Qed.

(** Source for [finite_coordinate_inverse_system]: the spaces X_a, a
    in A, with the projections p^b_a form a compact Hausdorff inverse
    system, Federer 2.6.6, pp. 120–121. *)
Theorem finite_coordinate_inverse_system :
  (forall i, hausdorff_space (Y i)) -> (forall i, compact (@setT (Y i))) ->
  is_compact_inverse_system finite_coordinate_subset (@finite_coordinate_bonding).
Proof.
move=> hh hc; split.
- split.
  + by exists fset0.
  + by move=> F j.
  + by move=> F G H hFG hGH j hj; apply: hGH; apply: hFG.
  + move=> F G; exists (F `|` G); split; [exact: fset_subset_unionl|exact: fset_subset_unionr].
- move=> F; exact: (@finite_coordinate_space_compact I Y hc F).
- move=> F; exact: (@finite_coordinate_space_hausdorff I Y hh F).
- move=> F G _ u; apply: continuous_comp.
  + exact: finite_coordinate_section_continuous.
  + exact: finite_coordinate_projection_continuous.
- move=> F u; exact: finite_coordinate_section_projection.
- move=> F G H hFG hGH u.
  have hFH : {subset F <= H} by move=> j hj; apply: hGH; apply: hFG.
  rewrite (finite_coordinate_bonding_restriction hGH) (finite_coordinate_bonding_restriction hFG).
  rewrite (finite_coordinate_bonding_restriction hFH).
  apply: functional_extensionality_dep=> -[j hj].
  rewrite /finite_coordinate_restriction /=.
  exact: finite_coordinate_coordinate_irrelevance.
Qed.

(** Source for [finite_coordinate_inverse_limit]: "the representation
    of X as inverse limit of the spaces X_a", Federer 2.6.6, p. 120:
    X with the projections p_a is the compact Hausdorff inverse limit
    of the system of the spaces X_a. *)
Theorem finite_coordinate_inverse_limit :
  (forall i, hausdorff_space (Y i)) -> (forall i, compact (@setT (Y i))) ->
  is_compact_inverse_limit finite_coordinate_subset (@finite_coordinate_bonding)
    (fun F=>finite_coordinate_projection (F:=F)).
Proof.
move=> hh hc; split.
- exact: compact_factor_product_compact hc.
- exact: hausdorff_product hh.
- move=> F; exact: finite_coordinate_projection_continuous.
- move=> x F G hFG; rewrite (finite_coordinate_bonding_restriction hFG).
  exact: finite_coordinate_restriction_projection.
- move=> u hu.
  exists (fun j=>u [fset j] (exist _ j (fset11 j)))=> F.
  apply: functional_extensionality_dep=> -[j hj].
  have h1 : {subset [fset j] <= F} by move=> k; rewrite in_fset1=> /eqP ->.
  rewrite /finite_coordinate_projection /= -(hu [fset j] F h1).
  rewrite (finite_coordinate_bonding_restriction h1) /finite_coordinate_restriction /=.
  exact: finite_coordinate_coordinate_irrelevance.
- move=> x y hxy; apply: functional_extensionality_dep=> j.
  exact: (congr1 (fun v : finite_coordinate_space Y [fset j] => v (exist _ j (fset11 j))) (hxy [fset j])).
Qed.
End FiniteInverseSystem.
