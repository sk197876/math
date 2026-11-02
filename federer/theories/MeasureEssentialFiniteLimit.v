(** Federer (1969), 2.4.12, pp. 86–87: L-infinity membership and
    completeness. Partial domains follow Federer; the erratum's total-domain
    restriction applies to the separate vector-space/seminorm assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureEssentialNorm MeasureEssentialNormAttainment
  MeasureEssentialNormComparison MeasureEssentialConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_reverse_triangle_bound]:
    supporting estimate for finite-norm membership of the limit
    in Federer 2.4.12, p. 87. The two domains
    need only be conull. *)
Lemma measure_essential_reverse_triangle_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X V) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  measure_essential_norm mu N g <= measure_essential_norm mu N f +
    measure_essential_distance mu N f g.
Proof.
move=> hf hg; have hd : measure_almost_everywhere mu
  (partial_function_domain (partial_vector_subtract f g)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hf hg)).
  move=> x [[y hy] [z hz]]; exists (y-z)%R.
  apply/partial_vector_subtract_graph; exists y,z; by split=> //; split.
have hbf := @measure_essential_norm_almost_bound R X V mu hm N f hf.
have hbd := @measure_essential_norm_almost_bound R X V mu hm N (partial_vector_subtract f g) hd.
apply: (@measure_essential_norm_of_almost_bound R X V mu hm N g _).
- apply: adde_ge0; exact: measure_essential_norm_nonnegative.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hbf hbd)).
  move=> x [[y [hy hfy]] [d [/partial_vector_subtract_graph [a [b [ha [hb ed]]]] hdd]]].
  have ea := partial_function_single_valued hy ha.
  exists b; split=> //.
  have hn : (N b <= N y + N d)%R.
    rewrite ed -ea (real_seminorm_subtract hN).
    have ht := real_seminorm_triangle hN y (b-y)%R.
    by rewrite addrC subrK in ht.
  apply: (le_trans (y:= (N y+N d)%:E)); first by rewrite lee_fin.
  rewrite EFinD; exact: leeD hfy hdd.
Qed.

(** Source for [essential_norm_limit_finite]: supporting finite
    norm of a limit of finite-norm functions in Federer 2.4.12,
    p. 87. One sufficiently late finite member and a finite
    error suffice; convergence supplies that error. *)
Lemma essential_norm_limit_finite (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X V) (g : partial_function X V) :
  (forall n, measure_almost_everywhere mu (partial_function_domain (f n))) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  (forall n, measure_essential_norm mu N (f n) < +oo) ->
  converges_in_essential_norm mu N f g -> measure_essential_norm mu N g < +oo.
Proof.
move=> hf hg hfinite hc; have [K hK] := hc 1%R (ltr01).
have he := hK K (leqnn K).
have hb := @measure_essential_reverse_triangle_bound R X V N hN mu hm (f K) g (hf K) hg.
apply: le_lt_trans hb _.
apply: lte_add_pinfty (hfinite K) _.
exact: lt_trans he (ltry (1%R)).
Qed.
