(** Federer (1969), 2.5.3, p. 94, third further condition. These supporting
    sum laws connect suiting sequences and positive support to that
    condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellCoverUP LatticeSeriesCoverUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_suiting_series_cover]: a suiting sequence dominates
    the characteristic function after summation; supporting Federer 2.5.3,
    p. 94, third condition. *)
Lemma daniell_suiting_series_cover (R : realType) (X : Type)
    (L : set (X -> R)) (T : set X) (f : nat -> X -> R) :
  is_daniell_suiting_sequence L T f -> is_positive_lattice_series_cover L T f.
Proof.
move=> hf; split; first exact hf.1.
move=> x hx.
have hnon := @nonnegative_sum_nonnegative R nat setT (fun n => (f n x)%:E).
case he: (nonnegative_sum setT (fun n => (f n x)%:E))=> [c| |]; last by move: hnon; rewrite he.
2: exact: leey.
rewrite lee_fin leNgt; apply/negP=> hc.
have hmid := midf_lt hc.
have [n hn] := hf.2.2 x hx ((c+1)/2)%R hmid.2.
have hterm := @nonnegative_sum_term R nat setT (fun n => (f n x)%:E) n Logic.I.
rewrite he lee_fin in hterm.
have hbad := lt_le_trans (lt_trans hmid.1 hn) hterm.
by move: hbad; rewrite ltxx.
Qed.

(** Source for [positive_lattice_series_cover_positive_term]: a nonzero
    positive summand is necessary at every covered point; supporting Federer
    2.5.3, p. 94, third condition. *)
Lemma positive_lattice_series_cover_positive_term (R : realType) (X : Type)
    (L : set (X -> R)) (T : set X) (f : nat -> X -> R) :
  is_positive_lattice_series_cover L T f -> forall x, T x -> exists n, (0 < f n x)%R.
Proof.
move=> hf x hx; apply: contrapT=> hn.
have hzero n : f n x=0%R.
  have hnot : ~ (0 < f n x)%R.
    move=> hp; apply: hn; exists n; exact hp.
  apply/eqP; rewrite eq_le ((hf.1 n).2 x) andbT leNgt.
  apply/negP; exact hnot.
have hsum : nonnegative_sum setT (fun n => (f n x)%:E)=0.
  apply: nonnegative_sum_zero=> n _; by rewrite hzero.
have h := hf.2 x hx; by move: h; rewrite hsum lee_fin ler10.
Qed.
