(** Federer (1969), 2.2.9, p. 65: existence of the countable disjoint open
    refinement. Iterating a binary split on the remaining open piece gives
    all children; their closures are pairwise disjoint and remain in the
    parent. This private construction needs no separability or completeness.
    Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import NoIsolatedPoints DisjointOpenSplit OpenRefinementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_disjoint_refinement_exists]: supporting construction
    for Federer 2.2.9, p. 65. Split each nonempty open remainder into a
    child and a new remainder with disjoint closures; recurse on the latter.
    This gives infinitely many distinct children of uniformly small diameter
    without any separability premise. *)
Theorem open_disjoint_refinement_exists (R : realType) (T : metricType R)
    (hT : has_no_isolated_points T) (U : set T) e :
  open U -> U !=set0 -> 0 < e -> exists F, is_open_disjoint_refinement U e F.
Proof.
move=> ho hn he.
pose P := { A : set T | open A /\ A !=set0 }.
pose carrier (A : P) := proj1_sig A.
have hc (C : P) : exists AB : P * P,
    closure (carrier AB.1) `<=` carrier C /\
    closure (carrier AB.2) `<=` carrier C /\
    closure (carrier AB.1) `&` closure (carrier AB.2) = set0 /\
    forall x y, closure (carrier AB.1) x -> closure (carrier AB.1) y -> mdist x y < e.
  have [A [B [hAo [hBo [hAn [hBn [hAU [hBU [hdis [hAd hBd]]]]]]]]]] :=
    nonisolated_open_binary_split hT (proj2_sig C).1 (proj2_sig C).2 he.
  exists (exist _ A (conj hAo hAn), exist _ B (conj hBo hBn)).
  by split=> //; split=> //; split.
pose split C := projT1 (cid (hc C)).
have hsplit C : closure (carrier (split C).1) `<=` carrier C /\
    closure (carrier (split C).2) `<=` carrier C /\
    closure (carrier (split C).1) `&` closure (carrier (split C).2) = set0 /\
    forall x y, closure (carrier (split C).1) x -> closure (carrier (split C).1) y -> mdist x y < e.
  exact: projT2 (cid (hc C)).
pose root : P := exist _ U (conj ho hn).
pose remainder := nat_rect (fun _ => P) root (fun _ C => (split C).2).
pose F n := carrier (split (remainder n)).1.
have hstep n : carrier (remainder n.+1) `<=` carrier (remainder n).
  move=> x hx; apply: (hsplit (remainder n)).2.1.
  exact: subset_closure hx.
have hnest i j : (i <= j)%N -> carrier (remainder j) `<=` carrier (remainder i).
  elim: j=> [|j IH] hij x hx.
  - have -> : i = 0%N by apply/eqP; rewrite -leqn0.
    exact hx.
  - case: (eqVneq i j.+1)=> [->|hine]; first exact hx.
    apply: IH; first by move: hij; rewrite leq_eqVlt (negbTE hine) /= ltnS.
    exact: hstep j x hx.
have hdis i j : (i < j)%N -> closure (F i) `&` closure (F j) = set0.
  move=> hij; apply/seteqP; split; last by move=> x [].
  move=> x [hxi hxj].
  have hxrem : carrier (remainder j) x := (hsplit (remainder j)).1 x hxj.
  have hxb : carrier (remainder i.+1) x := hnest i.+1 j hij x hxrem.
  have hxcl : closure (carrier (split (remainder i)).2) x := subset_closure hxb.
  have hh : (closure (carrier (split (remainder i)).1) `&`
      closure (carrier (split (remainder i)).2)) x by split.
  by rewrite (hsplit (remainder i)).2.2.1 in hh.
exists F; constructor.
- move=> n; exact: (proj2_sig (split (remainder n)).1).1.
- move=> n; exact: (proj2_sig (split (remainder n)).1).2.
- move=> n x hx; exact: (hnest 0%N n (leq0n n) x ((hsplit (remainder n)).1 x hx)).
- move=> i j hij; case: (ltngtP i j)=> h.
  + exact: hdis i j h.
  + rewrite setIC; exact: hdis j i h.
  + exfalso; exact: hij h.
- move=> n x y hx hy; exact: (hsplit (remainder n)).2.2.2 x y hx hy.
Qed.
