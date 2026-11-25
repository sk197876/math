(** Federer (1969), 4.1.27, p. 384:
    the final Hausdorff-density current identity
    holds for every original vertex family.
    Nondegeneracy gives the unit orientation; dependent
    vertices give the zero current and
    zero density. Keep those interpretations separate
    without strengthening the printed final identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ExteriorGrading CurrentSpaces CurrentDensityUP CurrentDensityAction CurrentDensitySealed
  CurrentDensityArithmetic CurrentDensityUniqueness CurrentSimplexFrame
  OrientedSimplexCurrentSealed OrientedSimplexDependentZero
  HausdorffMeasure CurrentLipschitzHausdorffDensity
  SimplexHausdorffDensityUP SimplexHausdorffDensitySealed
  SimplexHausdorffCurrent SimplexCubeDegeneracy CurrentZeroDensityLocalIntegrability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [simplex_hausdorff_current]: the full original
    identity [u_0,...,u_m]=H^m wedge eta
    in 4.1.27, p. 384, without
    a nondegeneracy premise. Every original input
    of the actual density current is
    derived; empty-product degree zero remains included. *)
Theorem simplex_hausdorff_current (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  exists hField:@is_locally_integrable_current_density R h2 n m
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (@SimplexHausdorffDensity.value R n m v),
    @OrientedSimplexCurrent.value R h2 n m v=
      @CurrentDensity.value R h2 n m
        (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
        (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
        (@current_area_hausdorff_measure_open_measurable R n m)
        (@SimplexHausdorffDensity.value R n m v) hField.
Proof.
case:(pselect (is_nondegenerate_current_simplex v))=>hCase.
- exact:(@simplex_hausdorff_current_density R h2 n m v hCase).
- pose H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
  pose hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
  pose hBorel:=@current_area_hausdorff_measure_open_measurable R n m.
  pose w:=@SimplexHausdorffDensity.value R n m v.
  have hW:w=(fun _=>0):=@simplex_hausdorff_density_degenerate_zero R n m v hCase.
  have hField:@is_locally_integrable_current_density R h2 n m H w.
    rewrite hW;exact:(@current_zero_density_locally_integrable R h2 n m H hH hBorel).
  have hAction:@is_current_density_action R h2 n m H w
      (@OrientedSimplexCurrent.value R h2 n m v).
    rewrite hW (@oriented_simplex_current_dependent_zero R h2 n m v hCase).
    exact:(@current_density_zero_action R h2 n m H hH).
  exists hField.
  exact:(@current_density_action_unique R h2 n m H w
    (@OrientedSimplexCurrent.value R h2 n m v)
    (@CurrentDensity.value R h2 n m H hH hBorel w hField) hAction
    (@CurrentDensity.laws R h2 n m H hH hBorel w hField)).
Qed.

(** Source for [simplex_hausdorff_current_full_action]: every actual
    compact target test has the literal
    final Hausdorff integral of 4.1.27,
    p. 384, with all vertex
    families and all degrees retained. *)
Theorem simplex_hausdorff_current_full_action (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  @is_current_density_action R h2 n m
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (@SimplexHausdorffDensity.value R n m v)
    (@OrientedSimplexCurrent.value R h2 n m v).
Proof.
have[hField ->]:=@simplex_hausdorff_current R h2 n m v.
exact:CurrentDensity.laws.
Qed.
