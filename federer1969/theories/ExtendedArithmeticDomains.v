(** Federer (1969), 2.1.1, p. 51, and 2.3.2, p. 74: the defined domains of
    extended-real arithmetic are Borel. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals
  TopologicalBorel BorelFamilyBasic BorelFunctionBasic TopologicalProductMaps BorelBooleanSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_order_singleton_borel]: supporting singleton
    calculation for the exceptional arithmetic pairs in Federer 2.3.2, p. 74 *)
Lemma extended_order_singleton_borel (R : realType) (a : extended_real_line R) :
  borel_set [set y : extended_real_line R | y == a].
Proof.
have he : [set y : extended_real_line R | y == a] = [set y | y <= a] `&` [set y | a <= y].
  apply/seteqP; split=> y; rewrite /= eq_le; [by move/andP|by move=> h; apply/andP].
rewrite he; apply: (borel_family_binary_intersection (borel_sets_family (extended_real_line R)));
  apply: closed_borel_set; [exact: order_closed_lower_ray_closed|exact: order_closed_upper_ray_closed].
Qed.

(** Source for [extended_first_coordinate_equal_borel]: supporting
    first-coordinate exceptional set for Federer 2.3.2, p. 74 *)
Lemma extended_first_coordinate_equal_borel (R : realType) (a : extended_real_line R) :
  borel_set [set p : extended_real_line R * extended_real_line R | p.1 == a].
Proof.
have hf := @continuous_borel_function
  [the topologicalType of (extended_real_line R * extended_real_line R)%type]
  (extended_real_line R) (@fst (extended_real_line R) (extended_real_line R))
  (@first_projection_continuous (extended_real_line R) (extended_real_line R)).
exact (@borel_function_preimage _ _ _ hf _ (@extended_order_singleton_borel R a)).
Qed.

(** Source for [extended_second_coordinate_equal_borel]: supporting
    second-coordinate exceptional set for Federer 2.3.2, p. 74 *)
Lemma extended_second_coordinate_equal_borel (R : realType) (a : extended_real_line R) :
  borel_set [set p : extended_real_line R * extended_real_line R | p.2 == a].
Proof.
have hf := @continuous_borel_function
  [the topologicalType of (extended_real_line R * extended_real_line R)%type]
  (extended_real_line R) (@snd (extended_real_line R) (extended_real_line R))
  (@second_projection_continuous (extended_real_line R) (extended_real_line R)).
exact (@borel_function_preimage _ _ _ hf _ (@extended_order_singleton_borel R a)).
Qed.

(** Source for [extended_add_domain_borel]: direct Borel-domain observation
    used for addition in Federer 2.3.2, p. 74 *)
Lemma extended_add_domain_borel (R : realType) :
  borel_set [set p : extended_real_line R * extended_real_line R | adde_def p.1 p.2].
Proof.
rewrite /adde_def; apply: borel_boolean_conjunction;
  apply: borel_boolean_negation; apply: borel_boolean_conjunction;
  [exact: extended_first_coordinate_equal_borel|exact: extended_second_coordinate_equal_borel|
   exact: extended_first_coordinate_equal_borel|exact: extended_second_coordinate_equal_borel].
Qed.

(** Source for [extended_multiply_domain_borel]: direct Borel-domain
    observation for multiplication in Federer 2.3.2, p. 74, with exactly the
    four zero/infinity pairs excluded. See the source header for the
    incorrect intersection sign. *)
Lemma extended_multiply_domain_borel (R : realType) :
  borel_set [set p : extended_real_line R * extended_real_line R | mule_def p.1 p.2].
Proof.
have he : (fun p : extended_real_line R * extended_real_line R => mule_def p.1 p.2) =
  (fun p => ~~ ((p.1 == 0) && ((p.2 == +oo) || (p.2 == -oo)) ||
               (p.2 == 0) && ((p.1 == +oo) || (p.1 == -oo)))).
  apply: funext=> p; case: p=> x y; case: x=> [x| |]; case: y=> [y| |]; by rewrite /mule_def /= ?orbF ?andbT ?andbF ?orbT ?eqxx.
change (borel_set [set p | (fun q : extended_real_line R * extended_real_line R => mule_def q.1 q.2) p]).
rewrite he; apply: borel_boolean_negation; apply: borel_boolean_disjunction;
  apply: borel_boolean_conjunction.
- exact: extended_first_coordinate_equal_borel.
- apply: borel_boolean_disjunction; exact: extended_second_coordinate_equal_borel.
- exact: extended_second_coordinate_equal_borel.
- apply: borel_boolean_disjunction; exact: extended_first_coordinate_equal_borel.
Qed.
