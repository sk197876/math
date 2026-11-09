(** Federer (1969), 3.3.19, p. 305: original child
    indices have the exact mass determined by their count. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP CircularDiscTreeExactCount
  CircularDiscSubfamilyMass HausdorffMeasure.
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
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_child_subfamily_mass]: the
    actual H1 mass of original A in any indexed subfamily
    of F_n(B) equals 2 rho_n times its actual cardinality,
    supporting both estimates in 3.3.19, p. 305.
    Actual centre injectivity discharges the no-duplicate condition. *)
Theorem circular_disc_child_subfamily_mass j (z:E) (F:{fset 'I_(j+4)}):
  z \in H j ->
  mu (A `&` (\bigcup_(k in [set` F])
    metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1)))=
    (2* rho j.+1*#|` F|%:R)%:E.
Proof.
move=>hz.
pose C:{fset E}:=[fset circular_disc_child_center z (rho j) k | k in F].
have hInside:(C `<=` H j.+1)%fset.
  apply/fsubsetP=>w /imfsetP[k hk ->].
  rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
  by exists z,k;split.
have hRadius:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hSubdivision:(4<=j+4)%N:= leq_addl j 4.
have hCard:#|` C|=#|` F|.
  rewrite /C card_imfset;last exact:(@circular_disc_child_center_injective R z (rho j) (j+4)%N hRadius hSubdivision).
  exact:erefl.
have hUnion:(\bigcup_(w in [set` C]) metric_closed_ball w (rho j.+1))=
  (\bigcup_(k in [set` F]) metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1)).
  apply/seteqP;split.
  - move=>x [w hw hx];move/imfsetP:hw=>[k hk hW];exists k=>//;by rewrite -hW.
  - move=>x [k hk hx];exists (circular_disc_child_center z (rho j) k)=>//.
    apply/imfsetP;by exists k.
have hMass:= @circular_disc_level_subfamily_mass R H hH A hA j.+1 C hInside.
by rewrite hUnion hCard in hMass.
Qed.
End Mass.
