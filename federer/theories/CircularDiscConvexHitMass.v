(** Federer (1969), 3.3.19, p. 303: exact
    radius-weighted halfplane count in the original outside-
    centre alternative. The coefficient is the printed
    1/2+1/n for n children of the original B. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls InnerConvex
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularDiscTreeUP
  CircularDiscHitCount CircularDiscHitMeasureUP CircularDiscConvexHitBound FiniteCellHitMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_convex_outside_hit_mass]:
    psi_(n+1)(B intersect S)<= (1/2+1/(n+1))rho_n
    in 3.3.19, p. 303, with book
    parent level n=j+3. The independent original
    psi laws and actual geometric count discharge every
    weight and integer rounding input. *)
Theorem circular_disc_convex_outside_hit_mass j (z:E) (S:set E):
  z \in H j ->S!=set0 ->is_inner_convex S ->~S z ->
  (psi j.+1 (metric_closed_ball z (rho j) `&` S)<=
    ((1/2+(j+4)%:R^-1)* rho j)%:E)%E.
Proof.
move=>hz hNonempty hConvex hzOutside.
have hCount:=@circular_disc_convex_outside_hit_count R H hH j z S hz hNonempty hConvex hzOutside.
pose M:nat:=#|` @circular_disc_hit_indices R H j.+1 (metric_closed_ball z (rho j) `&` S)|.
have hReal:(2* M%:R<=(j+4)%:R+2:>R).
  have hCast:(((2* M)%N)%:R<=(((j+4)+2)%N)%:R:>R) by rewrite ler_nat.
  by rewrite natrM natrD in hCast.
have hPositive:=@factorial_disc_radius_positive R N rho hs j.+1.
have hScaled:=ler_wpM2r (ltW hPositive) hReal.
have hNN:((j+4)%:R:R)!= 0 by rewrite pnatr_eq0 addn_eq0 andbF.
have hBudget:(j+4)%:R* rho j.+1=rho j by rewrite (factorial_disc_radius_step hs) mulrC (divfK hNN).
have hTarget:(1/2+(j+4)%:R^-1)* rho j=rho j/2+rho j.+1.
  rewrite (factorial_disc_radius_step hs);ring.
rewrite (hPsi j.+1) lee_fin.
change (is_true ((M%:R* rho j.+1)<=((1/2+(j+4)%:R^-1)* rho j))).
rewrite hTarget;nra.
Qed.
End Mass.
