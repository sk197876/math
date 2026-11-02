(** Federer (1969), 2.5.14, p. 108: the test f and tests supported outside
    its support give the lower bound alpha(W) >= lambda(f)+alpha(W minus
    support f). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactOpenContentUP
  FunctionLatticeUP MonotoneDaniellIntegralUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_disjoint_test_sum]: the admissibility of f+g
    when g is supported in W minus support f, used in Federer 2.5.14, p. 108 *)
Lemma compact_open_disjoint_test_sum (R : realType) (X : topologicalType)
    (W : set X) (f g : X -> R) :
  is_compact_open_test_function W f ->
  is_compact_open_test_function (W `\` real_function_support f) g ->
  is_compact_open_test_function W (fun x => (f x+g x)%R).
Proof.
move=> [hf [hb hs]] [hg [hc ht]].
split; first exact: (@function_lattice_add R X _ (@compactly_supported_continuous_functions_lattice R X) f g hf hg).
split.
- move=> x; have [hf0 hf1] := andP (hb x); have [hg0 hg1] := andP (hc x).
  apply/andP; split; first exact: addr_ge0 hf0 hg0.
  case: (pselect (real_function_support f x))=> hx.
  + have hg0' : g x=0%R.
      apply: real_function_zero_off_support=> hxg; exact: (ht x hxg).2 hx.
    by rewrite hg0' addr0.
  + by rewrite (real_function_zero_off_support hx) add0r.
- have hsub : real_function_support (fun x => (f x+g x)%R) `<=`
      real_function_support f `|` real_function_support g.
    apply: (@real_function_support_in_closed_set R X _ _
      (closedU (@real_function_support_closed R X f) (@real_function_support_closed R X g)))=> x hx.
    have hnf : ~ real_function_support f x by move=> h; apply: hx; left.
    have hng : ~ real_function_support g x by move=> h; apply: hx; right.
    by rewrite (real_function_zero_off_support hnf) (real_function_zero_off_support hng) addr0.
  move=> x hx; case: (hsub x hx)=> h; [exact: hs x h|exact: (ht x h).1].
Qed.

(** Source for [compact_open_content_disjoint_test_bound]: the inequality
    alpha(W) >= lambda(f)+alpha(W minus support f) in Federer 2.5.14, p. 108
    Infinite open costs are allowed. *)
Lemma compact_open_content_disjoint_test_bound (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R)
    (hA : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) W f :
  open W -> is_compact_open_test_function W f ->
  a (W `\` real_function_support f)+(A f)%:E <= a W.
Proof.
move=> hW hf.
have hU : open (W `\` real_function_support f).
  apply: openI=> //; rewrite openC; exact: real_function_support_closed.
rewrite -leeBrDr //; apply: (extended_real_supremum_least (ha _ hU))=> c [g [hg ->]].
rewrite leeBrDr // -EFinD.
have hsum := @compact_open_disjoint_test_sum R X W f g hf hg.
rewrite addrC -(@monotone_daniell_integral_add R X _ A hA f g hf.1 hg.1).
apply: (extended_real_supremum_upper (ha W hW)); exists (fun x => (f x+g x)%R); by split.
Qed.

(** Source for [compact_open_content_strict_approximation]: choosing the
    test f with value close to alpha(W intersection V), as in Federer
    2.5.14, p. 108 This is a consequence of supremum laws, with no
    implementation-dependent selection. *)
Lemma compact_open_content_strict_approximation (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R) (ha : is_compact_open_content A a) V c :
  open V -> c < a V -> exists f, is_compact_open_test_function V f /\ c < (A f)%:E.
Proof.
move=> hV hc; apply: contrapT=> hn.
have hb : a V <= c.
  apply: (extended_real_supremum_least (ha V hV))=> b [f [hf ->]].
  rewrite leNgt; apply/negP=> ht; apply: hn; exists f; by split.
by move: hc; rewrite ltNge hb.
Qed.
