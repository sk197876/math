(** Convex normal sections supporting Federer (1969), 2.10.30, p. 195, the
    assertion that Steiner symmetrisation preserves convexity. Convex
    combinations of points in two perpendicular sections belong to the
    section over the convex combination of their feet. This is proved from
    the project's convex-set laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import InnerConvex SteinerSymmetrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_section_convex_combination]: supporting
    affine-line identity for the convexity conclusion
    of 2.10.30, p. 195. No inner product
    or finite dimension is needed for this algebraic step. *)
Lemma normal_section_convex_combination (R : realType) (V : lmodType R)
    (u p q : V) (t a b : R) :
  (1-t)*:(p+a*:u)+t*:(q+b*:u)=
    ((1-t)*:p+t*:q)+((1-t)*a+t*b)*:u.
Proof. by rewrite !scalerDr !scalerA [((1-t)*a+t*b)*:u]scalerDl addrACA. Qed.

(** Source for [normal_scalar_section_convex]: supporting
    convexity of each scalar section of a convex
    S in 2.10.30, p. 195. The section
    may be empty or fail to contain its endpoints. *)
Lemma normal_scalar_section_convex (R : realType) (V : lmodType R)
    (u y : V) (S : set V) : is_inner_convex S ->
  @is_inner_convex R R^o (normal_scalar_section u S y).
Proof.
move=> hS a b ha hb t ht0 ht1.
have hh := hS (y+a*:u) (y+b*:u) ha hb t ht0 ht1.
rewrite normal_section_convex_combination -scalerDl subrK scale1r in hh.
exact hh.
Qed.

(** Source for [normal_section_minkowski_inclusion]: supporting
    inclusion of weighted scalar-section sums in
    the intermediate section for convexity in
    2.10.30, p. 195. *)
Lemma normal_section_minkowski_inclusion (R : realType) (V : lmodType R)
    (u p q : V) (S : set V) (t : R) :
  is_inner_convex S -> 0<=t -> t<=1 ->
  forall a b, normal_scalar_section u S p a -> normal_scalar_section u S q b ->
    normal_scalar_section u S ((1-t)*:p+t*:q) ((1-t)*a+t*b).
Proof.
move=> hS ht0 ht1 a b ha hb.
have hh := hS (p+a*:u) (q+b*:u) ha hb t ht0 ht1.
by rewrite normal_section_convex_combination in hh.
Qed.
