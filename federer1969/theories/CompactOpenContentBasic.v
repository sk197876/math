(** Federer (1969), 2.5.14, pp. 107–108: elementary properties of alpha(V),
    before the countable-cover argument. All assertions here follow from the
    abstract supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactOpenContentUP
  FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_zero_test]: the zero function is admissible in
    every alpha(V) of Federer 2.5.14, p. 107 In particular the supremum's
    test family is never empty. *)
Lemma compact_open_zero_test (R : realType) (X : topologicalType) V :
  is_compact_open_test_function V (fun _ : X => (0%R : R)).
Proof.
split; first exact: compactly_supported_zero_function.
split; first by move=> x; rewrite lexx ler01.
have hs : real_function_support (fun _ : X => (0%R : R))=set0.
  rewrite /real_function_support.
  have he : [set x : X | (0%R : R)<>0%R]=set0 by apply/seteqP; split=> x; by [].
  by rewrite he closure0.
by rewrite hs; move=> x [].
Qed.

(** Source for [compact_open_content_nonnegative]: nonnegative range of
    alpha in Federer 2.5.14, p. 107 *)
Lemma compact_open_content_nonnegative (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R)
    (hA : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) V : open V -> 0 <= a V.
Proof.
move=> hV; apply: (extended_real_supremum_upper (ha V hV)).
exists (fun _ => 0%R); split; first exact: compact_open_zero_test.
rewrite (@monotone_daniell_integral_zero R X _ A hA _ (@compactly_supported_zero_function R X)); exact: erefl.
Qed.

(** Source for [compact_open_content_empty]: alpha(empty)=0 in the measure
    argument of Federer 2.5.14, p. 108 Only the zero function has empty
    support. *)
Lemma compact_open_content_empty (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R)
    (hA : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) : a set0=0.
Proof.
apply/eqP; rewrite eq_le (@compact_open_content_nonnegative R X A a hA ha set0 open0) andbT.
apply: (extended_real_supremum_least (ha set0 open0))=> c [f [[hf [_ hs]] ->]].
have he : f=(fun _ => 0%R).
  apply: funext=> x; apply: real_function_zero_off_support=> hx; exact: hs x hx.
rewrite he (@monotone_daniell_integral_zero R X _ A hA _ (@compactly_supported_zero_function R X)); exact: lexx.
Qed.

(** Source for [compact_open_content_mono]: inclusion of open sets enlarges
    the admissible test family in alpha(V), supporting Federer 2.5.14, p.
    107 *)
Lemma compact_open_content_mono (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R) (ha : is_compact_open_content A a) U V :
  open U -> open V -> U `<=` V -> a U <= a V.
Proof.
move=> hU hV hUV; apply: (extended_real_supremum_least (ha U hU))=> c [f [[hf [hb hs]] ->]].
apply: (extended_real_supremum_upper (ha V hV)); exists f; split=> //; split=> //; split=> //.
move=> x hx; exact: hUV x (hs x hx).
Qed.
