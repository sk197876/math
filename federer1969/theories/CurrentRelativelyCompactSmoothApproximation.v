(** Federer (1969), 4.1.14, p. 370: if the
    closure of the prescribed source neighbourhood Z is
    compact in U, admissible smooth approximants exist on
    that same Z. Apply the existing approximation theorem
    to Clos Z and restrict its genuine smooth family.
    The original convergence law still requires caps only
    on K; this existence proof supplies a common cap on Z. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP LipschitzBasic SmoothCompactSet
  SmoothClassOpenRestriction CurrentMapDifferential EuclideanHomOperator
  CurrentMapDifferentialOpenRestriction CurrentSmoothApproximationUP
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentRelativelyCompactSmoothApproximation.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable Z:set X.
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hClosureCompact:@compact (real_norm_metric_space hNX)
  (@closure (real_norm_metric_space hNX) Z).
Hypothesis hClosureU:@closure (real_norm_metric_space hNX) Z `<=` U.
Arguments hClosureU : clear implicits.
Variable K:smooth_compact_set hNX Z.

(** Source for [current_relatively_compact_smooth_approximation_with_bound_exists]:
    for the prescribed relatively compact open Z the
    approximants are smooth, V-valued and have a common
    Lipschitz constant, Federer 4.1.14, p. 370. The
    original differential and uniform approximation laws on
    K are included. Empty Z, K and V need
    no point choice; no convexity is assumed. *)
Theorem current_relatively_compact_smooth_approximation_with_bound_exists:
  exists g:nat->X->Y,
    @is_current_smooth_approximation R n nu Z V K f g /\
    exists c:R,0<=c /\
      (forall i,@is_metric_lipschitz_bound R
        (real_norm_metric_space hNX) (real_norm_metric_space hNY) Z (g i) c) /\
      forall i x,Z x->@euclidean_operator_norm R n nu
        (@current_map_differential R n nu Z (g i) x)<=c.
Proof.
pose KU:=@Build_smooth_compact_set R X NX hNX U
  (@closure (real_norm_metric_space hNX) Z) hClosureU hClosureCompact.
have[c [W [g [hLeast hApprox]]]]:=
  @current_lipschitz_compact_smooth_approximation_exists R n nu
    U V hU hV KU f hLocal hImage.
have hZW:Z `<=` W.
  move=>x hx;apply:(current_compact_smooth_domain_contains hApprox).
  exact:subset_closure hx.
have hClass i:norm_class_all_orders hNX hNY Z (g i).
  exact:(@smooth_class_open_restriction R X Y NX NY hNX hNY W Z (g i)
    hZW hZ (current_compact_smooth_class hApprox i)).
have hImageG:forall i x,Z x->V (g i x).
  move=>i x hx.
  exact:(@current_compact_smooth_image R n nu U V KU f c W g hApprox
    i x (hZW x hx)).
have hDifferential:forall i x,Z x->@euclidean_operator_norm R n nu
    (@current_map_differential R n nu Z (g i) x)<=c.
  move=>i x hx.
  rewrite (@current_map_differential_open_restriction R n nu Z W hZ hZW
    (g i) (current_compact_smooth_class hApprox i) x hx).
  exact:(@current_compact_smooth_differential_bound R n nu U V KU f c W g hApprox
    i x (hZW x hx)).
have hNonnegative:0<=c:=current_compact_smooth_bound_nonnegative hApprox.
exists g;split.
- constructor.
  + exact:hImageG.
  + exact:hClass.
  + exists c;split;first exact:hNonnegative.
    move=>i x hx;exact:hDifferential i x (smooth_compact_in_domain K x hx).
  + move=>epsilon hEpsilon.
    have[N hN]:=current_compact_smooth_uniform hApprox hEpsilon.
    exists N=>i hNi x hx.
    have hxClosure:smooth_compact_carrier KU x.
      exact:subset_closure (smooth_compact_in_domain K x hx).
    exact:(@hN i hNi x hxClosure).
- exists c;split;first exact:hNonnegative.
  split;last exact:hDifferential.
  move=>i.
  exact:(@metric_lipschitz_bound_restrict R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY)
    W Z (g i) c hZW (current_compact_smooth_lipschitz hApprox i)).
Qed.

(** Source for [current_relatively_compact_smooth_approximation_exists]:
    the prescribed Z admits the smooth sequence in
    the original defining convergence condition of Federer
    4.1.14, p. 370. No selected or enlarged source
    appears in the statement. *)
Theorem current_relatively_compact_smooth_approximation_exists:
  exists g:nat->X->Y,@is_current_smooth_approximation R n nu Z V K f g.
Proof.
have[g [hG hBound]]:=current_relatively_compact_smooth_approximation_with_bound_exists.
by exists g.
Qed.
End CurrentRelativelyCompactSmoothApproximation.
