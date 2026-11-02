(** Federer (1969), proof of 2.5.2, p. 92: positivity of costs and
    elementary consequences of the infimum formula. All statements use the
    abstract envelope, not its private construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws
  ExtendedRealBoundsUP ExtendedRealBounds ExtendedRealOrderLimit DaniellCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_sequence_cost_exists]: existence of the limiting
    cost used in Federer 2.5.2, p. 92 The supremum is supplied by the
    previously proved extended-real bound interface. *)
Lemma daniell_sequence_cost_exists (R : realType) (X : Type)
    (A : (X -> R) -> R) (f : nat -> X -> R) : exists c, is_daniell_sequence_cost A f c.
Proof.
exists (extended_real_sup [set z | exists n, z=(A (f n))%:E]); constructor.
- exact: extended_real_sup_upper.
- exact: extended_real_sup_least.
Qed.

(** Source for [daniell_sequence_cost_nonnegative]: positivity of the
    limiting costs in Federer 2.5.2, p. 92 *)
Lemma daniell_sequence_cost_nonnegative (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (S : set X) (f : nat -> X -> R) (c : \bar R) :
  is_daniell_suiting_sequence L S f -> is_daniell_sequence_cost A f c -> 0 <= c.
Proof.
move=> hs hc.
have hp : (0 <= A (f 0%N))%R := monotone_daniell_integral_nonnegative hL hA (hs.1 0%N).1 (hs.1 0%N).2.
have hb : (A (f 0%N))%:E <= c by apply: (extended_real_supremum_upper hc); exists 0%N.
apply: le_trans _ hb; by rewrite lee_fin.
Qed.

(** Source for [daniell_sequence_cost_limit]: the cost is the increasing
    limit printed in Federer 2.5.2, p. 92 This connects the abstract
    supremum specification to the book's limit notation. *)
Lemma daniell_sequence_cost_limit (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hA : is_monotone_daniell_integral L A) (S : set X) (f : nat -> X -> R) (c : \bar R) :
  is_daniell_suiting_sequence L S f -> is_daniell_sequence_cost A f c ->
  extended_increases_to (fun n => (A (f n))%:E) c.
Proof.
move=> hs hc; apply: extended_increasing_supremum_limit _ hc=> n m hnm.
rewrite lee_fin; exact: (@monotone_daniell_integral_monotone R X L A hA (f n) (f m)
  (hs.1 n).1 (hs.1 m).1 (hs.2.1 n m hnm)).
Qed.

(** Source for [daniell_suiting_sequence_subset]: a sequence suiting B also
    suits every subset of B, supporting the measure formula in Federer
    2.5.2, p. 92 *)
Lemma daniell_suiting_sequence_subset (R : realType) (X : Type)
    (L : set (X -> R)) (S T : set X) (f : nat -> X -> R) :
  S `<=` T -> is_daniell_suiting_sequence L T f -> is_daniell_suiting_sequence L S f.
Proof.
move=> hST [hf [hmon hc]]; split=> //; split=> // x hx; exact: hc x (hST x hx).
Qed.

(** Source for [daniell_cover_nonnegative]: nonnegativity in the measure
    assertion of Federer 2.5.2, p. 92 *)
Lemma daniell_cover_nonnegative (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) S : 0 <= mu S.
Proof.
apply: (daniell_cover_greatest hm)=> f c hs hc.
exact: (@daniell_sequence_cost_nonnegative R X L A hL hA S f c hs hc).
Qed.

(** Source for [daniell_cover_monotone]: supporting monotonicity of the set
    function in Federer 2.5.2, p. 92 *)
Lemma daniell_cover_monotone (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) S T : S `<=` T -> mu S <= mu T.
Proof.
move=> hST; apply: (daniell_cover_greatest hm)=> f c hs hc.
exact: (daniell_cover_lower hm (daniell_suiting_sequence_subset hST hs) hc).
Qed.

(** Source for [daniell_constant_sequence_cost]: a constant sequence has its
    fixed functional value as cost, supporting the estimates in Federer
    2.5.2, pp. 92–93 *)
Lemma daniell_constant_sequence_cost (R : realType) (X : Type)
    (A : (X -> R) -> R) (f : X -> R) :
  is_daniell_sequence_cost A (fun _ : nat => f) (A f)%:E.
Proof.
constructor.
- by move=> z [n ->].
- move=> b hb; apply: hb; by exists 0%N.
Qed.

(** Source for [daniell_cover_empty]: zero mass of the empty set in Federer
    2.5.2, p. 92 A supplied lattice member records the nonempty-case
    restriction in that proof. *)
Lemma daniell_cover_empty (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) : L f -> mu set0=0.
Proof.
move=> hf; pose z := fun _ : X => (0%R : R).
have hz : L z := function_lattice_zero hL hf.
have hs : is_daniell_suiting_sequence L set0 (fun _ : nat => z).
  split.
  - move=> n; split=> // x; exact: lexx.
  - split; first by move=> n m hnm x; exact: lexx.
    by move=> x [].
have hc := @daniell_constant_sequence_cost R X A z.
have hA0 : A z=0%R := monotone_daniell_integral_zero hA hf.
rewrite hA0 in hc.
apply/eqP; rewrite eq_le (daniell_cover_nonnegative hL hA hm) andbT.
exact: (daniell_cover_lower hm hs hc).
Qed.

(** Source for [daniell_cover_approximation]: choosing suiting sequences
    with costs close to phi(B_i) in Federer 2.5.2, p. 92 *)
Lemma daniell_cover_approximation (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) S b : mu S < b ->
  exists f c, is_daniell_suiting_sequence L S f /\ is_daniell_sequence_cost A f c /\ c < b.
Proof.
move=> hb; apply: contrapT=> hn.
have hbm : b <= mu S.
  apply: (daniell_cover_greatest hm)=> f c hf hc.
  rewrite leNgt; apply/negP=> hlt; apply: hn; exists f, c; by split=> //; split.
by move: hb; rewrite ltNge hbm.
Qed.
