(** Federer (1969), 2.6.6, pp. 120–121, last paragraph: "The same type of
    reasoning can be applied to arbitrary inverse limits of Daniell
    integrals on lattices of continuous functions on compact Hausdorff
    spaces." The inverse limit is specified abstractly by
    [is_compact_inverse_limit]. This file proves that every compact
    Hausdorff inverse system has such a limit: the set of compatible
    families is closed in the cartesian product of the spaces, hence compact
    by Tychonoff's theorem, and with the induced topology and the restricted
    coordinate maps it satisfies the specification. The subspace is used
    only inside the existence proof. General topology background: the
    Tychonoff product theorem, Kelley, General Topology, Dover 2017 reprint
    of 1955, Chapter 5, p. 143. *)
From mathcomp Require Import all_boot boolp classical_sets functions topology subtype_topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseCompatibilityFinite
  NormalizedProductSpace SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compatible_inverse_families_closed]: the compatible
    families form a closed subset of the cartesian product, supporting
    the inverse limits of Federer 2.6.6, pp. 120–121. *)
Lemma compatible_inverse_families_closed (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i) :
  is_compact_inverse_system le b ->
  closed [set u : prod_topology Y | compatible_inverse_family le b u].
Proof.
move=> hs.
have -> : [set u : prod_topology Y | compatible_inverse_family le b u]=
    \bigcap_(ij in [set: (I * I)%type]) inverse_compatibility_constraint le b ij.
  apply/seteqP; split=> u hu.
  - by move=> [i j] _ hij; exact: hu i j hij.
  - by move=> i j hij; exact: (hu (i,j) Logic.I hij).
by apply: closed_bigI=> ij _; exact: inverse_compatibility_constraint_closed hs ij.
Qed.

(** Source for [compact_inverse_limit_exists]: every compact
    Hausdorff inverse system has an inverse limit in the sense of
    [is_compact_inverse_limit], as presupposed by the last paragraph of
    Federer 2.6.6, pp. 120–121. *)
Theorem compact_inverse_limit_exists (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i) :
  is_compact_inverse_system le b ->
  exists (X : topologicalType) (p : forall i, X -> Y i), is_compact_inverse_limit le b p.
Proof.
move=> hs.
pose S := [set u : prod_topology Y | compatible_inverse_family le b u].
have hcS : compact S.
  exact: subclosed_compact (compatible_inverse_families_closed hs)
    (compact_factor_product_compact (compact_inverse_system_compact hs)) (@subsetT _ S).
have hval : continuous (set_val : set_type S -> prod_topology Y) by exact: initial_continuous.
exists (set_type S); exists (fun i (x : set_type S)=>set_val x i); split.
- exact: set_type_compact_whole hcS.
- exact: set_type_hausdorff (hausdorff_product (compact_inverse_system_hausdorff hs)).
- move=> i x; exact: continuous_comp (hval x) (@proj_continuous I Y i (set_val x)).
- by move=> x i j hij; have hx := set_valP x; exact: hx i j hij.
- by move=> u hu; exists (exist _ u (mem_set hu)).
- move=> x y hxy; apply/val_inj; apply: functional_extensionality_dep=> i; exact: hxy i.
Qed.
