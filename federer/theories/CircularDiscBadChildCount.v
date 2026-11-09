(** Federer (1969), 3.3.19, p. 305: an actual child
    whose radial image meets the complement of a proper arc
    is counted with its original index, including contacts. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesSealed RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscRadialMapUP CircularDiscRadialIntervals
  PartialFunctionUP RegularGridAvoidanceCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BadChildren.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Variable H:nat->{fset E}.
Variable j:nat.
Variable eta:partial_function E E.
Hypothesis hEta:is_circular_disc_radial_map H j eta.

(** Source for [circular_disc_bad_child_indices]: the actual
    children whose original eta_n images meet the complement
    of the given arc, the selection in K_n of 3.3.19,
    p. 305. No selected point or direction is exposed. *)
Definition circular_disc_bad_child_indices (z:E) (a b:R):{fset 'I_(j+4)}:=
  [fset k:'I_(j+4) | `[<exists x v:E,
    metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1) x /\
    partial_function_graph eta x v /\~circular_parameter_arc a b v>]].

(** Source for [circular_disc_bad_child_count]: at most the
    complementary arc fraction plus 2/n of the actual
    original children can be selected, supporting the printed
    exceptional-stage estimate in 3.3.19, p. 305.
    The actual original arc is parametrized by 0<=a<=b<=2pi. *)
Theorem circular_disc_bad_child_count (z:E) (a b:R):
  z \in H j ->0<=a ->a<=b ->b<=2* p ->
  #|` circular_disc_bad_child_indices z a b|%:R/(j+4)%:R<=
    1-(b-a)/(2* p)+2/(j+4)%:R.
Proof.
move=>hz ha hab hb.
pose n:nat:=(j+4)%N.
pose q:R:= 2* p/n%:R.
pose e:R:= p/(2* n%:R).
pose F:= circular_disc_bad_child_indices z a b.
have hp:0<p:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hNP:(0<n%:R:>R) by rewrite ltr0n /n addn_gt0 orbT.
have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
have hpN:p!=0 by rewrite gt_eqF.
have hPiN:(2* p)!=0 by rewrite gt_eqF //;nra.
have hq:0<q by rewrite /q divr_gt0 // mulr_gt0 // ltr0n.
have he:0<e by rewrite /e divr_gt0 // mulr_gt0 // ltr0n.
have hBudget:q* n%:R= 2* p by rewrite /q divfK.
have hHalf:e= q/4 by rewrite /e /q;field.
have hTheta (k:'I_(j+4)):q* k%:R= 2* p* k%:R/(j+4)%:R by rewrite /q /n;ring.
have hCount:(#|` F|%:R<=n%:R:>R).
  have hU:(F `<=` [fset k | k:'I_(j+4)])%fset.
    apply/fsubsetP=>k _;apply/imfsetP;by exists k.
  have hC:= fsubset_leq_card hU.
  have hTotal:#|` [fset k | k:'I_(j+4)]|= n.
    rewrite card_imfset //= -cardE card_ord;exact:erefl.
  rewrite hTotal in hC;by rewrite ler_nat.
case:(leP (a+e) (b-e))=>hWidth.
- have hA:0<=a+e by lra.
  have hB:b-e<=q* n%:R by rewrite hBudget;lra.
  have hAvoid (k:'I_(j+4)):a+e<=q* k%:R ->q* k%:R<=b-e ->k \notin F.
    move=>hLeft hRight;apply/negP=>hk.
    move:hk;rewrite /F /circular_disc_bad_child_indices in_fset /= =>/asboolP[x [v [hx [hGraph hOutside]]]].
    apply:hOutside.
    have hLeftOriginal:a+e<=2* p* k%:R/(j+4)%:R by rewrite -hTheta.
    have hRightOriginal:2* p* k%:R/(j+4)%:R<=b-e by rewrite -hTheta.
    exact:(@circular_disc_child_radial_interval R H j eta hEta a b e z k hz
      (lexx _) hLeftOriginal hRightOriginal x v hx hGraph).
  have hGrid:= @regular_grid_avoidance_count R q n F (a+e) (b-e) hq hA hWidth hB hAvoid.
  have hReal:#|` F|%:R* q<=2* p-(b-a)+2* q by rewrite hBudget in hGrid;nra.
  have hInverse:0<(2* p)^-1 by rewrite invr_gt0;nra.
  have hScaled:= ler_wpM2r (ltW hInverse) hReal.
  have hLeft:(#|` F|%:R* q)*(2* p)^-1=#|` F|%:R/n%:R.
    rewrite /q;field.
    by rewrite ?hNN ?hpN.
  have hRight:(2* p-(b-a)+2* q)*(2* p)^-1= 1-(b-a)/(2* p)+2/n%:R by rewrite /q;field;by rewrite ?hNN ?hpN.
  by rewrite hLeft hRight in hScaled.

- have hSmall:b-a<=2* q by rewrite hHalf in hWidth;nra.
  have hScale:1-(b-a)/(2* p)+2/n%:R= 1+(2* q-(b-a))/(2* p).
    rewrite /q;field;by rewrite ?hNN ?hpN.
  have hNonnegative:0<=(2* q-(b-a))/(2* p) by apply:divr_ge0;[lra|nra].
  have hCountFraction:(#|` F|%:R/n%:R<=1:>R) by rewrite ler_pdivrMr // mul1r.
  change (is_true (#|` F|%:R/n%:R<=1-(b-a)/(2* p)+2/n%:R)).
  rewrite hScale;lra.
Qed.
End BadChildren.
