(** Federer (1969), 3.4.8(10), p. 332:
    choose disjoint source neighbourhoods of
    the finitely many fibre points. Apply
    the project's finite metric separation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology lra.
From Federer Require Import FiniteMetricSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_disjoint_metric_balls]:
    disjoint open neighbourhoods U_1,...,U_nu
    in 3.4.8(10), p. 332.
    A common radius below one third
    of the proved separation suffices. Empty
    and singleton families remain admissible. *)
Theorem finite_disjoint_metric_balls (R:realType) (X:metricType R)
    (I:finType) (a:I->X):
  injective a ->exists r:R,0<r /\
    forall i j,i!=j ->forall x,mdist (a i) x<r ->~(mdist (a j) x<r).
Proof.
move=>hInjective.
have hFinite:finite_set (a @` setT):=finite_image a (@finite_finset I setT).
pose F:=fset_set (a @` setT).
have hMember i:a i \in F.
  rewrite /F in_fset_set //;apply/mem_set;by exists i.
have [d [hD hSeparate]]:=@finite_metric_points_separated R X F.
pose r:R:=d/3.
have hR:0<r by rewrite /r divr_gt0 // ltr0n.
exists r;split;first exact:hR.
move=>i j hIJ x hIX hJX.
have hDifferent:a i!=a j by rewrite (inj_eq hInjective).
have hLower:=hSeparate (a i) (a j) (hMember i) (hMember j) hDifferent.
have hTriangle:=metric_triangle (a i) x (a j).
rewrite (metric_sym x (a j)) in hTriangle.
have hTwo:r+r<d by rewrite /r;lra.
have hBad:d<d by lra.
by rewrite ltxx in hBad.
Qed.
