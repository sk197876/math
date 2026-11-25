(** Federer (1969), 3.2.48, p. 284: the positive Haar/Hausdorff
    normalization retains Borel regularity. Supporting the actual
    probability average on p. 286, by the Borel-hull specification
    of 2.2.3, p. 61, and positive scaling of 2.1.2, p. 54. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureScaleIntegral BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [measure_scale_borel_regular]: positive normalization
    preserves actual Borel hulls and open-set measurability, supporting
    the Haar average in 3.2.48, pp. 284, 286. *)
Theorem measure_scale_borel_regular (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) c:
  (0<c)%R ->is_borel_regular_measure mu ->is_borel_regular_measure (measure_scale c mu).
Proof.
move=>hc hReg; constructor.
- move=>U hU; exact (@measure_scale_measurable R X mu hm c U (borel_regular_open_measurable hReg hU)).
- move=>A; have [B [hAB [hB hMass]]]:=borel_regular_cover hReg A.
  exists B; split; first exact hAB.
  split; first exact hB.
  by rewrite /measure_scale hMass.
Qed.
