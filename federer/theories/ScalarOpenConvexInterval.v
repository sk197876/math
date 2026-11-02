(** Federer (1969), 3.2.35, p. 272:
    a nonempty bounded open convex line section
    is an open interval with two actual endpoints.
    These are supporting scalar facts for the
    printed boundary-fibre multiplicity two. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealOpenIntervals InnerConvex ScalarConvexLength
  ScalarConvexSectionLength CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_open_member_neighbours]:
    supporting strict endpoint inequalities for
    the convex line fibres of Federer 3.2.35,
    p. 272. Original openness gives points
    on both sides of each original member,
    before any infimum or endpoint is chosen. *)
Lemma scalar_open_member_neighbours (R:realType) (A:set (real_line_metric R)) x:
  open A ->A x ->exists e:R,0<e /\A (x-e) /\A (x+e).
Proof.
move=>hOpen hx.
have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
  (x:real_line_metric R) A) (open_nbhs_nbhs (conj hOpen hx)).
pose e:R:=d/2.
have he:0<e by rewrite /e divr_gt0 // ltr0n.
have heSmall:e<d by rewrite /e ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
exists e; split; first exact he; split; apply:hBall.
- change (is_true (`|x-(x-e)|<d)).
  by rewrite opprB addrC subrK (ger0_norm (ltW he)).
- change (is_true (`|x-(x+e)|<d)).
  by rewrite opprD addrA subrr add0r normrN (ger0_norm (ltW he)).
Qed.

(** Source for [scalar_open_member_strict_bounds]:
    supporting exclusion of the two endpoint
    parameters from an original open line section
    in Federer 3.2.35, p. 272. Boundedness
    supplies its actual infimum and supremum laws;
    two-sided openness makes both inequalities strict. *)
Lemma scalar_open_member_strict_bounds (R:realType) (A:set (real_line_metric R)) x:
  open A ->metric_set_bounded A ->A x ->inf A<x /\x<sup A.
Proof.
move=>hOpen hBound hx.
have [hLower hUpper]:=bounded_scalar_order_bounds hBound.
have [e [he [hLeft hRight]]]:=scalar_open_member_neighbours hOpen hx.
have hl:=ge_inf hLower hLeft.
have hu:=ub_le_sup hUpper hRight.
split; lra.
Qed.

(** Source for [scalar_open_convex_interval]: supporting
    the two endpoints of every interior projection
    fibre in Federer 3.2.35, p. 272.
    The original nonempty bounded open convex set
    equals (inf A,sup A), with distinct actual
    endpoints. Convexity fills the intervening segment;
    no attained infimum, closed section or extra
    interval representation is assumed. *)
Theorem scalar_open_convex_interval (R:realType) (A:set (real_line_metric R)):
  A!=set0 ->open A ->@is_inner_convex R R^o A ->metric_set_bounded A ->
  inf A<sup A /\A=real_open_interval (inf A) (sup A).
Proof.
move=>hNonempty hOpen hConvex hBound.
have [hLower hUpper]:=bounded_scalar_order_bounds hBound.
have [x0 hx0]:=hNonempty.
have [hLeft hRight]:=scalar_open_member_strict_bounds hOpen hBound hx0.
split; first exact:(lt_trans hLeft hRight).
apply/seteqP; split=>x.
- exact:(scalar_open_member_strict_bounds hOpen hBound).
- move=>[hxLower hxUpper].
  have hInf:has_inf A by split.
  have he:0<x-inf A by rewrite subr_gt0.
  have [a ha hClose]:=inf_adherent he hInf.
  have hax:a<x by lra.
  have [b hb hxb]:=@sup_gt R A x hNonempty hxUpper.
  apply:(@real_convex_contains_segment R A a b hConvex ha hb
    (le_trans (ltW hax) (ltW hxb))).
  change (is_true (a<=x<=b)).
  by apply/andP; split; exact:ltW.
Qed.

(** Source for [scalar_bounded_endpoints_closure]: supporting
    the actual endpoint boundary points in Federer
    3.2.35, p. 272. Every nonempty bounded
    real set has both infimum and supremum in
    its closure, by their actual adherence laws.
    This helper needs no openness or convexity. *)
Lemma scalar_bounded_endpoints_closure (R:realType) (A:set (real_line_metric R)):
  A!=set0 ->metric_set_bounded A ->
  closure A (inf A) /\closure A (sup A).
Proof.
move=>hNonempty hBound.
have [hLower hUpper]:=bounded_scalar_order_bounds hBound.
have hInf:has_inf A by split.
have hSup:has_sup A by split.
split=>U hU.
- have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
    (inf A:real_line_metric R) U) hU.
  have [x hx hClose]:=inf_adherent hd hInf.
  have hLowerX:=ge_inf hLower hx.
  have hNonnegative:0<=x-inf A by rewrite subr_ge0.
  exists x; split; first exact hx; apply:hBall.
  change (is_true (`|inf A-x|<d)).
  rewrite distrC (ger0_norm hNonnegative); lra.
- have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
    (sup A:real_line_metric R) U) hU.
  have [x hx hClose]:=sup_adherent hd hSup.
  have hUpperX:=ub_le_sup hUpper hx.
  have hNonnegative:0<=sup A-x by rewrite subr_ge0.
  exists x; split; first exact hx; apply:hBall.
  change (is_true (`|sup A-x|<d)).
  rewrite (ger0_norm hNonnegative); lra.
Qed.
