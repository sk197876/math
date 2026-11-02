(** Federer (1969), 2.4.12, pp. 86–87, seminorm assertion at p=infinity,
    with erratum p. 1 book p. 86 bottom: use total functions for literal
    vector-space laws. We prove these endpoint laws on all total functions,
    hence also on the measurable total subspace of 2.3.8. This strengthening
    requires no measurability: null superlevel sets suffice. Source
    editions: MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP ExtendedSeminormUP PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureEssentialNorm MeasureEssentialNormComparison
  MeasureEssentialNormTriangle MeasureEssentialNormScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_measure_essential_norm]: phi_(infinity)
    restricted to total functions as required by Federer's erratum
    p. 1, book p. 86 bottom, for 2.4.12. *)
Definition total_measure_essential_norm (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (f : X -> V) :=
  measure_essential_norm mu N (partial_function_total f).

(** Source for [total_measure_essential_norm_seminorm]: the
    complete p=infinity seminorm laws in Federer 2.4.12,
    pp. 86–87, with the total-domain erratum correction.
    They hold even on all total functions; restricting to the
    measurable subspace gives precisely the book's assertion. *)
Theorem total_measure_essential_norm_seminorm (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  @is_extended_seminorm R (GRing.Lmodule.clone R (X -> V) _)
    (@total_measure_essential_norm R X V mu N).
Proof.
have hd (f : X -> V) : measure_almost_everywhere mu (partial_function_domain (partial_function_total f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (f x); by [].
constructor.
- move=> f; exact: measure_essential_norm_nonnegative.
- move=> c f; rewrite /total_measure_essential_norm.
  rewrite -(@measure_essential_norm_scale R X V N hN mu hm c (partial_function_total f) (hd f)).
  apply: (@measure_essential_norm_graph_equivalent R X V mu hm N _ _)=> x y.
  rewrite partial_vector_scale_graph; split.
  + move=> hy; exists (f x); split=> //; by symmetry.
  + move=> [z [hz hy]]; change (c *: f x = y)%R; by rewrite hy -hz.
- move=> f g; rewrite /total_measure_essential_norm.
  have he : measure_essential_norm mu N (partial_function_total (fun x => (f x+g x)%R)) =
      measure_essential_norm mu N (partial_vector_add (partial_function_total f) (partial_function_total g)).
    apply: (@measure_essential_norm_graph_equivalent R X V mu hm N _ _)=> x y.
    rewrite partial_vector_add_graph; split.
    + move=> hy; exists (f x),(g x); split=> //; split=> //; by symmetry.
    + move=> [a [b [ha [hb hy]]]]; change (f x + g x = y)%R; by rewrite hy -ha -hb.
  rewrite he; exact (@measure_essential_norm_triangle R X V N hN mu hm _ _ (hd f) (hd g)).
Qed.
