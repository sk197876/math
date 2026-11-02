(** Federer (1969), 2.10.41, printed p. 200: choose at most n+1 contact
    centres and nonnegative weights of total one representing the minimum
    centre. This supporting finite-dimensional convex-hull fact is proved
    locally by the existing coefficient elimination, after translating one
    generator to zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import LinearBasis InnerConvex ConvexHull ConvexFiniteCombinations ConvexTranslatedCombinations
  SubconvexCombinations SubconvexReduction InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_hull_translated_subconvex]: supporting
    translation used in the finite contact representation
    of 2.10.41, p. 200. Derive the representation
    from the abstract least-convex-superset laws, without
    inspecting the sealed hull implementation. *)
Lemma convex_hull_translated_subconvex (R : realFieldType) (V : lmodType R)
    (A : set V) (a b : V) :
  A a -> convex_hull A b -> subconvex_combinations [set z | A (z+a)] (b-a).
Proof.
move=> ha hb.
pose D := [set z | A (z+a)].
have h0 : D 0 by rewrite /D /= add0r.
have hC : is_inner_convex [set x | subconvex_combinations D (x-a)].
  exact: (@convex_translate_to_origin R V (subconvex_combinations D) (-a)
    (@subconvex_combinations_convex R V D)).
have hAC : A `<=` [set x | subconvex_combinations D (x-a)].
  move=> x hx; apply: subconvex_combinations_include.
  by rewrite /D /= subrK.
exact (@convex_hull_least R V A _ hAC hC b hb).
Qed.

(** Source for [convex_hull_finite_support]: supporting finite
    convex-combination choice in 2.10.41, p. 200 At most d+1 points suffice
    for a space with a d-element basis. Zero weights, repeated points and
    dimension zero are allowed; affine independence is unnecessary for the
    application. *)
Theorem convex_hull_finite_support (R : realFieldType) (V : lmodType R)
    d (e : 'I_d -> V) (A : set V) (b : V) :
  is_basis e -> A !=set0 -> convex_hull A b ->
  exists k : nat, exists u : 'I_k -> V, exists w : 'I_k -> R,
    (0<k<=d.+1)%N /\ (forall i, A (u i)) /\ (forall i, 0<=w i) /\
    (\sum_i w i= 1) /\ b=\sum_i w i*:u i.
Proof.
move=> he [a ha] hb.
have [m [v [q [hv [hq [hs hvalue]]]]]] := convex_hull_translated_subconvex ha hb.
pose D := [set z | A (z+a)].
have [k [z [c [hk [hz [hc [hcs hzc]]]]]]] :=
  @subconvex_dimension_reduction R V d e he D m v q hv hq hs.
have hrepr : b-a=\sum_i c i*:z i := eq_trans hvalue hzc.
pose u := ordinal_snoc (fun i : 'I_k=>z i+a) a.
pose w := ordinal_snoc c (1-\sum_i c i).
exists k.+1,u,w; split; first by rewrite ltn0Sn /=.
split.
- move=> i; case: (unliftP ord_max i)=> [j ->|->].
  + rewrite /u ordinal_snoc_lift; exact: hz.
  + by rewrite /u ordinal_snoc_last.
split.
- move=> i; case: (unliftP ord_max i)=> [j ->|->].
  + rewrite /w ordinal_snoc_lift; exact: hc.
  + by rewrite /w ordinal_snoc_last subr_ge0.
split.
- rewrite /w big_ord_recr ordinal_snoc_last.
  under eq_bigr do rewrite ordinal_snoc_before.
  change ((\sum_i c i)+(1-\sum_i c i)= 1).
  by rewrite addrC subrK.
- rewrite /w /u big_ord_recr !ordinal_snoc_last.
  under eq_bigr do rewrite !ordinal_snoc_before scalerDr.
  rewrite big_split -scaler_suml.
  change (b=(\sum_i c i*:z i)+(\sum_i c i)*:a+(1-\sum_i c i)*:a).
  have hadd : (\sum_i c i)+(1-\sum_i c i)= 1 by rewrite addrC subrK.
  by rewrite -addrA -scalerDl hadd scale1r -hrepr subrK.
Qed.
