(** Federer (1969), 2.10.1, p. 170, last paragraph: local counterexample to
    extending the printed open covers of A literally to all topological
    spaces. This is distinct from the valid metric formula. In a two-point
    topology, the resulting infimum can increase on passing to a subset, and
    therefore need not be a measure. The local erratum p. 3, book p. 170
    lines 24 and 35, corrects the references to Federer1955 Theorem 2.5, pp.
    291–292; it does not give this correction. The concrete topology is
    hidden behind its sealed laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport ExtendedRealBounds
  OpenRefinementBoundUP TwoPointOpenTopologyUP TwoPointOpenTopologySealed
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [printed_open_refinement_value]: literal
    threshold infimum of the alternative expression in Federer
    2.10.1, p. 170. This expression agrees with the
    metric construction there; calling it a measure on an
    arbitrary topological space requires a separate proof and
    is refuted below for this literal A-cover convention. *)
Definition printed_open_refinement_value (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) (A : set X) :=
  extended_real_inf [set t | is_open_refinement_bound S cost A t].

(** Source for [proper_open_single_generator_refinement_infinite]:
    supporting obstruction for the local counterexample to
    Federer 2.10.1, p. 170. A sole whole-space generator
    cannot refine the singleton family consisting of a proper
    nonempty open set A. No threshold then has the printed
    property, so its infimum is positive infinity. *)
Lemma proper_open_single_generator_refinement_infinite (R : realType) (X : topologicalType)
    (A : set X) (c : \bar R) : open A -> (exists x, A x) -> (exists y, ~ A y) ->
  printed_open_refinement_value (fun _ : unit => @setT X) (fun _ => c) A=+oo.
Proof.
move=> hA [x hx] [y hy]; apply/eqP; rewrite eq_le leey /=.
apply: extended_real_inf_greatest=> t ht.
have hopen U : [set A] U -> open U by move=> ->.
have hcover : A `<=` \bigcup_(U in [set A]) U by move=> z hz; exists A.
have [G [_ [hG [href _]]]] := ht [set A] hopen hcover.
have [j hj _] := hG x hx.
have [U [hU hSU]] := href j hj.
exfalso; apply: hy; rewrite -hU; exact: hSU y I.
Qed.

(** Source for [single_generator_refinement_whole_mass]:
    supporting whole-space value for the local counterexample
    to Federer 2.10.1, p. 170. If p has no proper open
    neighbourhood, every open cover of X contains X itself.
    The sole generator X of cost one then has raw value one. *)
Lemma single_generator_refinement_whole_mass (R : realType) (X : topologicalType) (p : X) :
  (forall U : set X, open U -> U p -> U=setT) ->
  printed_open_refinement_value (fun _ : unit => @setT X) (fun _ => (1 : \bar R)) setT = 1.
Proof.
move=> hp; apply/eqP; rewrite eq_le; apply/andP; split.
- apply/lee_addgt0Pr=> e he.
  apply: extended_real_inf_lower=> H hopen hcover.
  have [U hU hpU] := hcover p I.
  have hUT := hp U (hopen U hU) hpU.
  exists [set tt]; split; first exact: countable1.
  split; first by move=> x _; exists tt.
  split.
  + move=> j _; exists U; split=> //; by rewrite hUT.
  + rewrite nonnegative_sum_singleton // -EFinD lte_fin ltrDl; exact he.
- apply: extended_real_inf_greatest=> t ht.
  have hopen U : [set (@setT X)] U -> open U by move=> ->; exact: openT.
  have hcover : (@setT X) `<=` \bigcup_(U in [set (@setT X)]) U.
    by move=> x _; exists setT.
  have [G [_ [hG [_ hb]]]] := ht [set (@setT X)] hopen hcover.
  have [j hj _] := hG p I.
  have hterm := @nonnegative_sum_term R [the choiceType of (unit : Type)] G
    (fun _ => (1 : \bar R)) j hj.
  exact: ltW (le_lt_trans hterm hb).
Qed.

(** Source for [printed_topological_refinement_not_measure]:
    local counterexample to the arbitrary-topological-space
    claim in Federer 2.10.1, p. 170, with the literal
    printed quantifier over open covers of A. The sealed
    two-point space has a proper nonempty open singleton A.
    With X as the only generator, of cost one, the raw
    infimum assigns infinity to A and one to X. This
    violates monotonicity, hence the measure laws. *)
Theorem printed_topological_refinement_not_measure (R : realType) :
  let X := TwoPointOpenTopology.space in
  let mu := @printed_open_refinement_value R X [the choiceType of (unit : Type)]
    (fun _ => @setT X) (fun _ => (1 : \bar R)) in
  mu [set TwoPointOpenTopology.second]=+oo /\ mu setT = 1 /\ ~ is_measure mu.
Proof.
move=> X mu.
have hX := TwoPointOpenTopology.laws.
have hA : mu [set TwoPointOpenTopology.second]=+oo.
  apply: proper_open_single_generator_refinement_infinite.
  - exact: two_point_second_singleton_open hX.
  - by exists TwoPointOpenTopology.second.
  - exists TwoPointOpenTopology.first; exact: hX.1.
have hT : mu setT = 1.
  apply: (@single_generator_refinement_whole_mass R X TwoPointOpenTopology.first)=> U ho hp.
  exact: two_point_first_neighbourhood_whole hX ho hp.
split=> //; split=> // hm.
have hb := @measure_mono R X mu hm [set TwoPointOpenTopology.second] setT (fun _ _ => I).
by rewrite hA hT in hb.
Qed.
