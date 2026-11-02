(** Federer (1969), 2.6.6, p. 120: integration of all coordinates of a
    cylinder leaves a scalar, independent of the auxiliary point used to
    evaluate the remaining parameters. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp mathcomp_extra classical_sets reals topology.
From Federer Require Import ProductCylinderLattice CoordinateDaniellOperator FiniteCoordinateFunctionalConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [coordinate_fold_remaining_dependence]: supporting
    finite induction showing which coordinates remain after successive
    integrations, Federer 2.6.6, p. 120. *)
Lemma coordinate_fold_remaining_dependence (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (F : {fset I}) (f : prod_topology Y -> R) (s : seq I) :
  is_coordinate_determined F f -> forall x y,
    (forall i, i \in F -> i \notin s -> x i=y i) ->
    foldr (coordinate_daniell_operator A) f s x=foldr (coordinate_daniell_operator A) f s y.
Proof.
move=> hf; elim: s=> [|i s ih] x y hxy /=.
- apply: hf=> j hj; apply: hxy=> //; by rewrite in_nil.
- rewrite /coordinate_daniell_operator; congr (A i _); apply: funext=> u.
  apply: ih=> j hj hjs; case: (eqVneq i j)=> [<-|hij]; first by rewrite !dfwithin.
  rewrite !dfwithout //; apply: hxy=> //; by rewrite in_cons negb_or eq_sym hij hjs.
Qed.

(** Source for [finite_coordinate_functional_independent]: the finite
    product value on L_a does not depend on a point outside a,
    supporting the well-defined marginals in Federer 2.6.6, p. 120. *)
Theorem finite_coordinate_functional_independent (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (F : {fset I}) (f : prod_topology Y -> R) (x y : prod_topology Y) :
  is_coordinate_determined F f ->
  finite_coordinate_functional A x F f=finite_coordinate_functional A y F f.
Proof.
move=> hf; apply: (@coordinate_fold_remaining_dependence R I Y A F f (enum_fset F) hf x y).
by move=> i hi; rewrite hi.
Qed.
