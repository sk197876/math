(** Federer (1969), 2.4.12, pp. 86–87: supporting essential-norm
    comparisons. Source context and threshold convention:
    MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureNullModification MeasureGauge MeasureEssentialNormUP MeasureEssentialNorm MeasureEssentialNormAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm_superlevel_comparison]:
    supporting monotonicity of the defining infimum in Federer
    2.4.12, p. 86. *)
Lemma measure_essential_norm_superlevel_comparison (R : realType) (X : choiceType)
    (Y Z : Type) (mu : set X -> \bar R) (hm : is_measure mu)
    (N : Y -> R) (M : Z -> R) (f : partial_function X Y) (g : partial_function X Z) :
  (forall r, mu (partial_norm_superlevel N f r) <= mu (partial_norm_superlevel M g r)) ->
  measure_essential_norm mu N f <= measure_essential_norm mu M g.
Proof.
move=> h; apply: (measure_essential_norm_specification mu M g).2=> r [hr hg].
apply: measure_essential_norm_bound; split=> //.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -hg; exact: h.
- exact (@measure_nonnegative R X mu hm _).
Qed.

(** Source for [measure_essential_norm_almost_equal]: supporting
    invariance under almost equality for Federer 2.4.12,
    pp. 86–87, retaining the convention of 2.3.1,
    p. 72. *)
Lemma measure_essential_norm_almost_equal (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f g : partial_function X Y) :
  measure_almost_equal mu f g -> measure_essential_norm mu N f=measure_essential_norm mu N g.
Proof.
move=> he; have h r := @almost_equal_preimage_measure R X Y mu hm f g [set y | r < (N y)%:E] he.
apply/eqP; rewrite eq_le; apply/andP; split;
  apply: (@measure_essential_norm_superlevel_comparison R X Y Y mu hm N N _ _)=> r;
  by rewrite /partial_norm_superlevel h.
Qed.

(** Source for [measure_essential_norm_of_almost_bound]: supporting infimum
    consequence of the almost-everywhere bound in Federer 2.4.12, p. 86 The
    comparison constant may be infinite. *)
Lemma measure_essential_norm_of_almost_bound (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) c :
  0 <= c -> measure_almost_everywhere mu [set x | exists y,
    partial_function_graph f x y /\ (N y)%:E <= c] -> measure_essential_norm mu N f <= c.
Proof.
move=> hc hb; apply: measure_essential_norm_bound; split=> //.
apply: (@measure_null_subset R X mu hm _ _ _ hb).
move=> x [y [hy hcy]] [z [hz hzc]].
have he := partial_function_single_valued hy hz; rewrite -he in hzc.
have hbad := lt_le_trans hcy hzc.
by move: hbad; rewrite ltxx.
Qed.

(** Source for [measure_essential_norm_zero_iff]: supporting
    zero-norm criterion for the Lebesgue spaces in Federer
    2.4.12, pp. 86–87: the strict positive-norm
    locus is null exactly when the essential norm is zero. *)
Lemma measure_essential_norm_zero_iff (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) :
  measure_essential_norm mu N f = 0 <-> mu (partial_norm_superlevel N f 0) = 0.
Proof.
split.
- move=> hz; have h := (measure_essential_norm_attained hm N f).2; by rewrite hz in h.
- move=> hz; apply/eqP; rewrite eq_le measure_essential_norm_nonnegative andbT.
  apply: measure_essential_norm_bound; by split.
Qed.

(** Source for [measure_essential_norm_graph_equivalent]:
    supporting extensionality for the essential norm in Federer
    2.4.12, p. 86. Exact graph equivalence preserves
    each superlevel even for a nonconull domain. *)
Lemma measure_essential_norm_graph_equivalent (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f g : partial_function X Y) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  measure_essential_norm mu N f=measure_essential_norm mu N g.
Proof.
move=> he; have hsets r : partial_norm_superlevel N f r=partial_norm_superlevel N g r.
  apply/seteqP; split=> x [y [hy hr]]; exists y; split=> //; [exact: (he x y).1 hy|exact: (he x y).2 hy].
apply/eqP; rewrite eq_le; apply/andP; split;
  apply: (@measure_essential_norm_superlevel_comparison R X Y Y mu hm N N _ _)=> r; by rewrite hsets.
Qed.
