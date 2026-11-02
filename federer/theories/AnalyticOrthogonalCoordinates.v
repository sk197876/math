(** Federer (1969), 3.1.24, p. 240, referring to 3.1.19, p. 231: condition (5) implies (4).
    Shrink inside the given neighbourhood, without assuming that the
    original neighbourhood T is open. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex
  NormDifferentialUP NormClassOneUP NormClassZeroTopology NormRegularity
  NormRegularityOperations NormFiniteLinearBound NormOpenDomainLaws NormLinearDomainLaws
  EuclideanSubmanifoldUP SubmanifoldChartsUP NormAnalyticUP NormAnalyticLocal NormAnalyticLinear NormAnalyticOperations AnalyticSubmanifoldChartsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_orthogonal_graphs_convex_coordinates]: 3.1.24, p. 240: implication
    (5) to (4), Federer 3.1.19, p. 231. A convex parameter ball and
    its ambient inverse image give open coordinate domains; the given
    inverse remains analytic after open restriction. *)
Theorem analytic_orthogonal_graphs_convex_coordinates (R:realType) n mu (B:set (R_n R n)) :
  @has_analytic_orthogonal_graphs R n mu B -> @has_analytic_convex_coordinates R n mu B.
Proof.
move=>hB b hb.
have [T [p [j [psi hchart]]]]:=hB b hb.
have [hTb [hj [hp [hinj [himage [hconv [hpsi [hrange [hcan [hinv hD]]]]]]]]]]:=hchart.
pose X:=R_n R n; pose Y:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hpsi1:=norm_analytic_class_all_orders hpsi 1%N.
have hbT:T b:=norm_domain_interior_member hNX hTb.
have hbP:(p @` T) (p b) by exists b.
have hpsib:psi (p b)=b:=hinv b (conj hb hbT).
have [r [hr hball]]:=hTb.
have [d [hd hcontrol]]:=@norm_class_zero_local_control R Y X NY NX hNY
  (p @` T) psi (p b) r (norm_class_continuous hpsi1) hbP hr.
pose V:=fun u:Y=>NY (u-p b)<d.
pose U:=fun x:X=>NX (x-b)<r /\ V (p x).
have hPV u (hu:V u):(p @` T) u:=(hcontrol u hu).1.
have hpsiU u (hu:V u):U (psi u).
  split.
  - by have hh:=(hcontrol u hu).2; rewrite hpsib in hh.
  - by rewrite /V hcan //; exact: hPV.
have hpb:norm_bounded_linear NX NY (hom_of_linear p).
  exact (@norm_finite_linear_bounded R X Y NX NY hNX hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) (hom_of_linear p)).
have hopenV u (hu:V u):norm_domain_interior NY V u.
  exact (@norm_open_ball_domain_interior R Y NY hNY (p b) d u hu).
have hopenU x (hx:U x):norm_domain_interior NX U x.
  apply: norm_domain_intersection_interior.
  - exact (@norm_open_ball_domain_interior R X NX hNX b r x hx.1).
  - exact (@norm_bounded_linear_preimage_interior R X Y NX NY hNX (hom_of_linear p)
      V x hpb (hopenV (p x) hx.2)).
have hbU:U b by split; [rewrite subrr /NX inner_norm0|rewrite /V subrr /NY inner_norm0].
have hpsiV:=@norm_analytic_open_restriction R Y X NY NX hNY hNX (p @` T) V psi
  hPV hopenV hpsi.
exists U,V,(fun x=>p x),psi; split; first exact: hopenU hbU.
split; first exact (@norm_open_ball_convex R Y NY hNY (p b) d).
split.
- exact (@norm_bounded_linear_analytic R X Y NX NY hNX hNY U hopenU (hom_of_linear p) hpb).
split=>//; split; first by move=>x hx; exact hx.2.
split; first exact hpsiU.
split; last by move=>u hu; exact: hcan (hPV u hu).
apply/seteqP; split=>x.
- move=>[u hu <-]; split; first exact (hrange u (hPV u hu)).1.
  exact: hpsiU.
- move=>[hBx hUx].
  have hTx:T x.
    have hh:=hball (x-b) hUx.1; by rewrite addrC subrK in hh.
  exists (p x); first exact hUx.2.
  exact: hinv (conj hBx hTx).
Qed.
