(** Private gluing construction for gamma in Federer (1969), 2.6.6, p. 120.
    Choice of a finite coordinate set is independent of its presentation by
    consistency on the union. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import ProductCylinderLattice ConsistentCylinderFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [cylinder_functional_gluing_exists]: existence of
    gamma agreeing with the finite marginals, Federer 2.6.6, p. 120.
    This construction uses only the supplied consistency laws. *)
Theorem cylinder_functional_gluing_exists (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : {fset I} -> (prod_topology Y -> R) -> R) :
  is_consistent_cylinder_functional_family A -> exists B, is_glued_cylinder_functional A B.
Proof.
move=> hA.
pose B := fun f : prod_topology Y -> R =>
  if pselect (continuous_product_cylinders f) is left hf then A (sval (cid hf.2)) f else 0.
exists B=> F f [hf hF]; rewrite /B; case: pselect=> [hd|hn]; last first.
  exfalso; apply: hn; split=> //; by exists F.
pose G := sval (cid hd.2).
have hG : is_coordinate_determined G f := svalP (cid hd.2).
have hFG : {subset F <= F `|` G} by move=> i hi; rewrite in_fsetU hi.
have hGF : {subset G <= F `|` G} by move=> i hi; rewrite in_fsetU hi orbT.
exact: eq_trans (esym (@cylinder_family_consistent R I Y A hA G (F `|` G) hGF f (conj hf hG)))
  (@cylinder_family_consistent R I Y A hA F (F `|` G) hFG f (conj hf hF)).
Qed.
