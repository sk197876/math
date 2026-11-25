(** Federer (1969), 3.3.4, pp. 290–291: positive
    finite mass of the actual projective unit-sphere image.
    It is derived from its exact mass formula, rather
    than postulated as a homogeneity or density hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  SymmetricGrading InnerSymmetricPositivity StructureProjectiveSphere
  HausdorffMeasure EuclideanBallVolume MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_projective_sphere_positive_finite]:
    the factor H^m[T(U)] in Federer 3.3.4,
    p. 290, is positive and finite. The actual
    unit sphere and two-to-one area identity give
    this in all natural dimensions, including m=0. *)
Theorem structure_projective_sphere_positive_finite (R:realType) m:
  0<@hausdorff_measure R
    (inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
      (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2))
    m (@structure_projective_sphere R m)< +oo.
Proof.
pose Y:=inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2).
pose H:=@hausdorff_measure R Y m.
pose M:=H (@structure_projective_sphere R m).
have hMass:((2:R)%:E*M)=((m.+1)%:R*euclidean_unit_ball_volume R m.+1)%R%:E:=
  @structure_projective_sphere_mass R m.
have hRight:(0<(m.+1)%:R*euclidean_unit_ball_volume R m.+1)%R.
  apply:mulr_gt0; first by rewrite ltr0n.
  exact:(euclidean_unit_ball_volumeE R m.+1).2.
have hPositive:0<M.
  rewrite lt_def (measure_nonnegative (@hausdorff_measure_is_measure R Y m)) andbT.
  apply/negP=>/eqP hZero.
  have h:=hMass; rewrite hZero mule0 in h.
  have hp:(0<((m.+1)%:R*euclidean_unit_ball_volume R m.+1)%R%:E) by rewrite lte_fin.
  by rewrite -h ltxx in hp.
apply/andP; split=>//.
have hFinite:(2:R)%:E*M< +oo by rewrite hMass ltry.
rewrite ltNge leye_eq; apply/negP=>/eqP he.
change (M=+oo) in he.
by move:hFinite; rewrite he gt0_muley ?lte_fin ?ltr0n // ltxx.
Qed.
