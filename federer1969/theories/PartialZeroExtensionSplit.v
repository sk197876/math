(** Federer (1969), 2.4.10, p. 85: supporting exact decomposition
    f=f_A+f_(X\A), used for splitting integral bounds and interval
    additivity. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic
  PartialZeroExtension PartialZeroExtensionLaws MeasureStepIntegralIdentification RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_zero_extension_split_graph]: exact
    pointwise decomposition underlying the splitting of subset
    integrals in Federer 2.4.10, p. 85. At each
    point one summand is zero, so no undefined infinite sum occurs. *)
Lemma partial_zero_extension_split_graph (R : realType) (X : Type)
    (A : set X) (f : partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_extended_function_add
    (partial_function_zero_extension (0 : extended_real_line R) A f)
    (partial_function_zero_extension (0 : extended_real_line R) (~` A) f)) x z <->
  partial_function_graph f x z.
Proof.
rewrite partial_extended_function_add_graph; have [hx|hx] := pselect (A x); split.
- move=> [a [b [ha [hb hab]]]].
  have hf := (@partial_function_zero_extension_on X (extended_real_line R) 0 A f x a hx).1 ha.
  have hnc : ~ (~` A) x by move=> hn; exact: hn hx.
  have eb := (@partial_function_zero_extension_off X (extended_real_line R) 0 (~` A) f x b hnc).1 hb.
  rewrite eb /extended_add fin_num_adde_defl // adde0 in hab; case: hab=> he; by rewrite -he.
- move=> hz; exists z,0; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split.
    * apply/partial_function_zero_extension_graph; right; split=> // hn; exact: hn hx.
    * by rewrite /extended_add fin_num_adde_defl // adde0.
- move=> [a [b [ha [hb hab]]]].
  have ea := (@partial_function_zero_extension_off X (extended_real_line R) 0 A f x a hx).1 ha.
  have hf := (@partial_function_zero_extension_on X (extended_real_line R) 0 (~` A) f x b hx).1 hb.
  rewrite ea /extended_add fin_num_adde_defr // add0e in hab; case: hab=> he; by rewrite -he.
- move=> hz; exists 0,z; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split.
    * apply/partial_function_zero_extension_graph; left; by split.
    * by rewrite /extended_add fin_num_adde_defr // add0e.
Qed.

(** Source for [zero_extension_real_embedding_graph]: compatibility
    of real step functions and extended-valued cutoffs in
    Federer 2.4.10, p. 85. *)
Lemma zero_extension_real_embedding_graph (R : realType) (X : Type)
    (A : set X) (u : partial_function X (real_line_metric R)) x y :
  partial_function_graph (partial_real_function_embed
    (partial_function_zero_extension (0%R : real_line_metric R) A u)) x y <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) A
    (partial_real_function_embed u)) x y.
Proof.
exact (@partial_zero_extension_postcompose X (real_line_metric R) (extended_real_line R)
  0%R 0 A u (fun r => r%:E) x y (erefl (0 : \bar R))).
Qed.
