(** Federer (1969), 2.6.6, p. 120: integrating a coordinate removes
    dependence on it, and adding an unused normalized factor leaves the
    functional unchanged. These are supporting steps in the finite-marginal
    consistency equation. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp mathcomp_extra classical_sets reals topology.
From Federer Require Import ProductCylinderLattice CoordinateDaniellOperator CompactSupportFunctionUP
  DaniellIntegralUP DaniellSpaceCompactness DaniellSpaceCompactSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [coordinate_daniell_operator_determined]: removing
    one coordinate from the dependence set under integration,
    supporting Federer 2.6.6, p. 120. No integral laws are needed
    for this equality of parameter functions. *)
Lemma coordinate_daniell_operator_determined (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (i : I) (F : {fset I}) (f : prod_topology Y -> R) :
  is_coordinate_determined F f ->
  is_coordinate_determined (F `\` [fset i]) (coordinate_daniell_operator A i f).
Proof.
move=> hf x y hxy; rewrite /coordinate_daniell_operator.
congr (A i _); apply: funext=> u; apply: hf=> j hj.
case: (eqVneq i j)=> [<-|hij]; first by rewrite !dfwithin.
rewrite !dfwithout //; apply: hxy; by rewrite in_fsetD in_fset1 eq_sym hij hj.
Qed.

(** Source for [coordinate_daniell_operator_unused]: the normalized
    unused factor contributes 1 in the consistency equation of
    Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_operator_unused (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (i : I) (F : {fset I}) (f : prod_topology Y -> R) :
  compact (@setT (Y i)) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i) ->
  A i (fun _=>1) = 1 -> i \notin F -> is_coordinate_determined F f ->
  coordinate_daniell_operator A i f=f.
Proof.
move=> hc hA hA1 hi hf; apply: funext=> x; rewrite /coordinate_daniell_operator.
have he : (fun u=>f (dfwith x i u))=(fun _ : Y i=>f x*1).
  apply: funext=> u; rewrite mulr1; apply: hf=> j hj.
  have hij : i != j by apply/negP=> /eqP he; move: hi; rewrite he hj.
  by rewrite dfwithout.
rewrite he ((@daniell_compact_support_linear R (Y i) (A i) hA).2
  (f x) (fun _=>1) (@compact_space_constant_one R (Y i) hc)).
by rewrite hA1 mulr1.
Qed.
