(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals topology.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeCountableLevels
  BoundedSupportContinuous BoundedOpenTests ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [bounded_continuous_open_increasing_levels]: supporting
    identification of F1 with the open sets for the lattice in
    Federer 2.9.10, p. 157. Every open set is a countable union
    of positive strict levels of bounded-support continuous tests:
    use integer-radius cutoffs and reciprocal thresholds, then
    finite unions as in 2.5.3. No countable-base or local-compactness
    hypothesis is introduced. *)
Theorem bounded_continuous_open_increasing_levels (R : realType) (X : metricType R)
    (a : X) (U : set X) :
  open U -> function_lattice_increasing_levels (@bounded_support_continuous_functions R X) U.
Proof.
move=> hU.
have hex n : exists f : X -> R,
    positive_function_lattice (@bounded_support_continuous_functions R X) f /\
    (forall x, U x /\ mdist a x<n.+1%:R <-> 0<f x).
  exact (@bounded_open_positive_test_exists R X a n.+1%:R U ltac:(by rewrite ltr0n) hU).
pose f n := projT1 (cid (hex n)).
have hf n : positive_function_lattice (@bounded_support_continuous_functions R X) (f n) /\
    (forall x, U x /\ mdist a x<n.+1%:R <-> 0<f n x) := projT2 (cid (hex n)).
pose F (p : nat*nat) := [set x | (p.2.+1%:R : R)^-1<f p.1 x].
pose C : set (set X) := F @` setT.
have hC : countable C := sub_countable (card_image_le F setT) (@countableP (nat*nat)%type setT).
have hlevels S : C S -> function_lattice_strict_levels (@bounded_support_continuous_functions R X) S.
  move=> [p _ <-]; exists (f p.1),((p.2.+1%:R : R)^-1); split; first exact: (hf p.1).1.
  split=> //; by rewrite invr_gt0 ltr0n.
have he : U=\bigcup_(S in C) S.
  apply/seteqP; split=> x.
  - move=> hx.
    pose n := Num.bound (mdist a x).
    have hn : mdist a x<n.+1%:R.
      apply: lt_le_trans (archi_boundP (mdist_ge0 a x)) _; by rewrite ler_nat.
    have hp := (hf n).2 x; have hfx := hp.1 (conj hx hn).
    have [k hk] := positive_reciprocal_nat_small hfx.
    exists (F (n,k)); last exact hk.
    exists (n,k)=> //.
  - move=> [S [p _ <-] hx].
    have hp0 : (0<(p.2.+1%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
    have hp : 0<f p.1 x := lt_trans hp0 hx.
    exact: (((hf p.1).2 x).2 hp).1.
rewrite he; exact (@function_lattice_countable_strict_levels_union R X _
  (@bounded_support_continuous_lattice R X) (fun _ => 0)
  C (@bounded_support_continuous_zero R X) hC hlevels).
Qed.
