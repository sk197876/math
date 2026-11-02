(** Federer (1969), 2.4.12, p. 87, first sentence, with the erratum p. 1
    book p. 86 bottom and p. 2 book p. 87 line 1: the infinity endpoint
    satisfies the seminorm inequalities. We state the triangle inequality
    for exact partial domains; a vector-space claim separately requires the
    corrected total-domain convention. Source context:
    MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureEssentialNorm MeasureEssentialNormAttainment MeasureEssentialNormComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm_triangle]: triangle
    inequality at p=infinity in Federer 2.4.12,
    pp. 86–87, on the common original domain of
    the summands. Their domains are only required to be conull. *)
Theorem measure_essential_norm_triangle (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X V) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  measure_essential_norm mu N (partial_vector_add f g) <=
    measure_essential_norm mu N f + measure_essential_norm mu N g.
Proof.
move=> hf hg; apply: (@measure_essential_norm_of_almost_bound R X V mu hm N (partial_vector_add f g) _).
- exact: adde_ge0 (measure_essential_norm_nonnegative mu N f) (measure_essential_norm_nonnegative mu N g).
- have hbf := @measure_essential_norm_almost_bound R X V mu hm N f hf.
  have hbg := @measure_essential_norm_almost_bound R X V mu hm N g hg.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hbf hbg)).
  move=> x [[y [hy hfy]] [z [hz hgz]]]; exists (y+z)%R; split.
  + apply/partial_vector_add_graph; exists y,z; by split=> //; split.
  + apply: (le_trans (y:= (N y+N z)%:E)).
    * rewrite lee_fin; exact (@real_seminorm_triangle R V N hN y z).
    * rewrite EFinD; exact: leeD hfy hgz.
Qed.
