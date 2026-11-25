(** Federer (1969), 2.6.6, p. 120: the finite marginals and their
    consistency. Finite products are realized by the successive integrations
    of 2.6.4; unused normalized factors contribute 1. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import ProductCylinderLattice ConsistentCylinderFunctionalUP CompactSupportFunctionUP
  CoordinateDaniellOperator CoordinateDaniellFoldConstruction CoordinateDaniellDependence FiniteSetEnumerationSplit
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [finite_coordinate_functional]: finite product
    functional on L_a in Federer 2.6.6, p. 120, computed by
    integrating precisely the coordinates in a. The chosen product
    point is an evaluation parameter for the construction. *)
Definition finite_coordinate_functional (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (x0 : prod_topology Y) (F : {fset I}) (f : prod_topology Y -> R) :=
  foldr (coordinate_daniell_operator A) f (enum_fset F) x0.

Section Consistency.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Variables (A : forall i, (Y i -> R) -> R) (x0 : prod_topology Y).
Hypotheses (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i))).
Hypothesis hX : compact (@setT (prod_topology Y)).
Hypothesis hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i).
Hypothesis hA1 : forall i, @A i (fun _=>1) = 1.
Arguments hh i : clear implicits.
Arguments hc i : clear implicits.
Arguments hA i : clear implicits.
Arguments hA1 i : clear implicits.
Local Notation U := (coordinate_daniell_operator A).

(** Source for [unused_coordinate_fold_identity]: integrating only
    unused coordinates leaves a cylinder function unchanged, the
    normalization step of Federer 2.6.6, p. 120. *)
Lemma unused_coordinate_fold_identity (s : seq I) (F : {fset I}) (f : prod_topology Y -> R) :
  (forall i, i \in s -> i \notin F) -> is_coordinate_determined F f -> foldr U f s=f.
Proof.
move=> hs hf; elim: s hs=> [|i s ih] hs //=.
have htail : forall j, j \in s -> j \notin F by move=> j hj; apply: hs; rewrite in_cons hj orbT.
rewrite (ih htail); exact (@coordinate_daniell_operator_unused R I Y A i F f (hc i)
  (monotone_daniell_integral_is_daniell (hA i)) (hA1 i) (hs i (mem_head _ _)) hf).
Qed.

(** Source for [finite_coordinate_functional_consistent]: exact
    compatibility under a contained in b, Federer 2.6.6, p. 120,
    proved by splitting the finite integrations into a and b-a. *)
Theorem finite_coordinate_functional_consistent (F G : {fset I}) (f : prod_topology Y -> R) :
  {subset F <= G} -> continuous_coordinate_functions F f ->
  finite_coordinate_functional A x0 G f=finite_coordinate_functional A x0 F f.
Proof.
move=> hFG [hf hdep]; rewrite /finite_coordinate_functional.
have he := @coordinate_daniell_fold_permutation R I Y A hh hc hX hA
  (enum_fset G) (enum_fset F ++ enum_fset (G `\` F)) f hf (finite_set_enumeration_split hFG).
rewrite he foldr_cat.
have hother : forall i, i \in (G `\` F) -> i \notin F.
  by move=> i; rewrite in_fsetD=> /andP[].
by rewrite (unused_coordinate_fold_identity hother hdep).
Qed.

(** Source for [finite_coordinate_functional_family]: all laws of
    the actual finite-product family used in Federer 2.6.6, p. 120.
    The consistency laws are proved from the factor Daniell integrals,
    rather than assumed for a new family. *)
Theorem finite_coordinate_functional_family :
  is_consistent_cylinder_functional_family (finite_coordinate_functional A x0).
Proof.
constructor.
- move=> F; split.
  + move=> f g [hf hF] [hg hG]; rewrite /finite_coordinate_functional
      (@coordinate_daniell_fold_add R I Y A hh hc hX hA (enum_fset F) f g hf hg); by [].
  + move=> c f [hf hF]; rewrite /finite_coordinate_functional
      (@coordinate_daniell_fold_scale R I Y A hh hc hX hA (enum_fset F) c f hf); by [].
- move=> F f g [hf hF] [hg hG] hfg.
  exact: (@coordinate_daniell_fold_monotone R I Y A hh hc hX hA (enum_fset F) f g hf hg hfg x0).
- move=> F; rewrite /finite_coordinate_functional (@coordinate_daniell_fold_one R I Y A hA1 (enum_fset F)); by [].
- move=> F G hFG f hf; exact (@finite_coordinate_functional_consistent F G f hFG hf).
Qed.
End Consistency.
