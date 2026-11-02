(** Federer (1969), 2.5.5, p. 97: applying the positive-variation argument
    to -mu supplies the negative variation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellIntegralAlgebra
  MonotoneDaniellIntegralUP ExtendedRealOrderLimit ExtendedRealDecreasingLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_integral_negate]: the assertion that -mu satisfies
    the same four hypotheses, Federer 2.5.5, p. 97 Ordinary convergence,
    rather than increasing convergence of values, is essential. *)
Theorem daniell_integral_negate (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  is_daniell_integral L (fun f => (- A f)%R).
Proof.
move=> hL hA; constructor.
- move=> f g hf hg; by rewrite (daniell_integral_add hA hf hg) opprD.
- move=> c f hc hf; by rewrite (daniell_integral_scale hA hc hf) mulrN.
- move=> f hf; have [b hb] := @daniell_integral_order_bounded R X L A hA f hf.
  exists (b-A f)%R.
  exact: (@daniell_integral_negative_order_bound R X L A hL hA f b hf hb).
- move=> f g hf hg hfg.
  exact: (@extended_order_limit_negate R (fun n => (A (f n))%:E) (A g)%:E
    (@daniell_integral_increasing_continuity R X L A hA f g hf hg hfg)).
Qed.

(** Source for [monotone_daniell_is_daniell]: relation between the two
    classes named in Federer 2.5.6, p. 97; supporting the comparison of
    2.5.2 and 2.5.5. *)
Lemma monotone_daniell_is_daniell (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_monotone_daniell_integral L A -> is_daniell_integral L A.
Proof.
move=> hA; constructor.
- exact: (@monotone_daniell_integral_add R X L A hA).
- exact: (@monotone_daniell_integral_scale R X L A hA).
- move=> f hf; exists (A f)=> k [hk [_ hkf]].
  exact: (@monotone_daniell_integral_monotone R X L A hA k f hk hf hkf).
- move=> f g hf hg hfg.
  exact: (@monotone_daniell_integral_increases R X L A hA f g hf hg hfg).2.
Qed.
