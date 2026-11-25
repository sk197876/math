(** Federer (1969), 2.5.3, pp. 94–95: positive lattice levels test
    measurability. We use the suiting-sequence argument behind (6) on a
    finite-measure test set and scale by two to obtain a countable
    closed-unit-level cover. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellCoverUP DaniellCoverBasic
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_finite_unit_level_cover]: supporting countable
    closed-unit-level cover for the last criterion in Federer 2.5.3, p. 94
    Only finite test-set measure is required. *)
Lemma daniell_finite_unit_level_cover (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hc : is_daniell_cover_envelope L A mu) (T : set X) :
  mu T < +oo -> exists f : nat -> X -> R,
    (forall n, positive_function_lattice L (f n)) /\
    T `<=` \bigcup_(n in setT) [set x | (1 <= f n x)%R].
Proof.
move=> hfin.
have hfinite : mu T \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm T).
have hstrict : mu T < (fine (mu T)+1)%R%:E.
  by rewrite -{1}(fineK hfinite) lte_fin ltrDl ltr01.
have [g [c [hg _]]] := daniell_cover_approximation hc hstrict.
have h2 : (0 < 2%R :> R)%R by rewrite ltr0n.
exists (fun n x => (2*g n x)%R); split.
- move=> n; exact: (@function_lattice_scale R X (positive_function_lattice L)
    (positive_function_lattice_laws hL) 2%R (g n) (ltW h2) (hg.1 n)).
- move=> x hx.
  have hhalf : (1/2 < 1 :> R)%R by rewrite (@ltr_pdivrMr R 2 1 1 h2) mul1r ltr1n.
  have [n hn] := hg.2.2 x hx (1/2)%R hhalf.
  exists n=> //; change (is_true ((1 <= 2*g n x)%R)).
  rewrite mulrC -(@ler_pdivrMr R 2 (g n x) 1 h2); exact: ltW hn.
Qed.
