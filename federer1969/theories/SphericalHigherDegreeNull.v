(** Federer (1969), 3.2.48, p. 285: null factors reduce
    the formula to zero equals zero. Degrees above the sphere's
    dimension are null by 2.10.2(1), p. 171, using the actual
    finite Gamma sphere mass from 3.2.13, p. 251. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric UnitSphereSpace
  HausdorffMeasure HausdorffDimensionDrop SphereGammaMass MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.

(** Source for [spherical_higher_degree_null]: the above-dimensional
    cases of 3.2.48, p. 284, following its null-factor observation
    on p. 285. No extra degree bound, measurability or source
    rectifiability premise is imposed for this nullity result. *)
Lemma spherical_higher_degree_null (R:realType) d r (A:set (R_n R (1+d))):
  (d<r)%N ->A `<=` @euclidean_unit_sphere_set R (1+d) ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) r A=0)%E.
Proof.
move=>hDegree hA.
pose X:=inner_metric_space (@euclidean_inner_productP R (1+d)).
have hMass:=@hausdorff_unit_sphere_gamma_mass R (1+d)%N (ltn0Sn d).
rewrite subn1 succnK in hMass.
have hFinite:(@hausdorff_measure R X d (@euclidean_unit_sphere_set R (1+d))< +oo)%E.
  by rewrite hMass ltry.
have hNull:=@hausdorff_finite_mass_higher_degree_zero R X d r
  (@euclidean_unit_sphere_set R (1+d)) hDegree hFinite.
exact (measure_null_subset (@hausdorff_measure_is_measure R X r) hA hNull).
Qed.
