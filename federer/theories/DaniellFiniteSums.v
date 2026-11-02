(** Federer (1969), proof of 2.5.2, p. 92: finite sums of suiting sequences
    and additivity of their functional values. These supporting finite-sum
    lemmas include the empty sum, with zero membership stated explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [function_lattice_sequence_sum]: membership of the finite
    diagonal sums in Federer 2.5.2, p. 92 *)
Lemma function_lattice_sequence_sum (R : realType) (X : Type) (J : eqType)
    (L : set (X -> R)) (hL : is_function_lattice L) (s : seq J) (f : J -> X -> R) :
  L (fun _ => 0%R) -> (forall j, j \in s -> L (f j)) ->
  L (fun x => (\sum_(j <- s) f j x)%R).
Proof.
move=> h0; elim: s=> [|j s ih] hf.
- have he : (fun x : X => (\sum_(j <- [::]) f j x)%R)=(fun _ => 0%R).
    by apply: funext=> x; rewrite big_nil.
  by rewrite he.
- have hs k : k \in s -> L (f k) by move=> hk; apply: hf; rewrite in_cons hk orbT.
  have hh := function_lattice_add hL (hf j (mem_head j s)) (ih hs).
  have he : (fun x => (\sum_(k <- j::s) f k x)%R)=(fun x => (f j x+\sum_(k <- s) f k x)%R).
    by apply: funext=> x; rewrite big_cons.
  by rewrite he.
Qed.

(** Source for [monotone_daniell_sequence_sum]: finite additivity display in
    Federer 2.5.2, p. 92 Empty sums use the proved zero-functional law. *)
Lemma monotone_daniell_sequence_sum (R : realType) (X : Type) (J : eqType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (s : seq J) (f : J -> X -> R) :
  L (fun _ => 0%R) -> (forall j, j \in s -> L (f j)) ->
  A (fun x => (\sum_(j <- s) f j x)%R)=(\sum_(j <- s) A (f j))%R.
Proof.
move=> h0; elim: s=> [|j s ih] hf.
- have he : (fun x : X => (\sum_(j <- [::]) f j x)%R)=(fun _ => 0%R).
    by apply: funext=> x; rewrite big_nil.
  rewrite he big_nil; exact: (@monotone_daniell_integral_zero R X L A hA (fun _ => 0%R) h0).
- have hs k : k \in s -> L (f k) by move=> hk; apply: hf; rewrite in_cons hk orbT.
  have hsum := function_lattice_sequence_sum hL h0 hs.
  have he : (fun x => (\sum_(k <- j::s) f k x)%R)=(fun x => (f j x+\sum_(k <- s) f k x)%R).
    by apply: funext=> x; rewrite big_cons.
  rewrite he (monotone_daniell_integral_add hA (hf j (mem_head j s)) hsum) (ih hs) big_cons.
  by [].
Qed.

(** Source for [finite_nonnegative_real_sum_term]: a diagonal sum dominates
    each included term in Federer 2.5.2, p. 92 *)
Lemma finite_nonnegative_real_sum_term (R : realType) (J : choiceType)
    (C : {fset J}) (u : J -> R) j :
  j \in C -> (forall i, i \in C -> (0 <= u i)%R) -> (u j <= \sum_(i <- C) u i)%R.
Proof.
move=> hj hu.
have hp i : i \in C -> (0 : \bar R) <= (u i)%:E by move=> hi; rewrite lee_fin; exact: hu.
have hh := @nonnegative_sum_term R J [set i | i \in C] (fun i => (u i)%:E) j hj.
by rewrite (nonnegative_sum_finite hp) sumEFin lee_fin in hh.
Qed.

(** Source for [finite_nonnegative_real_sum_subset]: enlarging the finite
    index set increases a positive sum, supporting the diagonal sequence in
    Federer 2.5.2, p. 92 *)
Lemma finite_nonnegative_real_sum_subset (R : realType) (J : choiceType)
    (C D : {fset J}) (u : J -> R) : (C `<=` D)%fset ->
  (forall i, i \in D -> (0 <= u i)%R) ->
  (\sum_(i <- C) u i <= \sum_(i <- D) u i)%R.
Proof.
move=> hCD hu.
have hsub i : i \in C -> i \in D := fun hi => fsubsetP hCD i hi.
have hpD i : i \in D -> (0 : \bar R) <= (u i)%:E by move=> hi; rewrite lee_fin; exact: hu.
have hpC i : i \in C -> (0 : \bar R) <= (u i)%:E by move=> hi; exact: hpD (hsub i hi).
have hh := @nonnegative_sum_subset R J [set i | i \in C] [set i | i \in D]
  (fun i => (u i)%:E) hsub.
by rewrite (nonnegative_sum_finite hpC) (nonnegative_sum_finite hpD) !sumEFin lee_fin in hh.
Qed.
