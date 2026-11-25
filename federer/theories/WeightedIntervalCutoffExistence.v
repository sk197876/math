(** Federer (1969), 4.1.12, p. 369:
    the actual original phi_k exist.
    Apply the preceding translated unit
    cutoff at q=k^(-3), retaining
    its exact support and derivative constant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces ReciprocalPowerSeriesBounds WeightedIntervalEndpoints
  CurrentScaledIntervalCutoff WeightedIntervalCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalCutoffExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation DT := (@current_test_space R h2 1%N Full hFull 0%N).

(** Source for [weighted_interval_cutoff_exists]: the
    original phi_k exists for every
    k>=1 with all printed exact
    bounds, Federer 4.1.12, p. 369. *)
Theorem weighted_interval_cutoff_exists n:exists phi:DT,@is_weighted_interval_cutoff R h2 n phi.
Proof.
pose q:=reciprocal_power_series_weight R 3%N n.
have hq:0<q:=reciprocal_power_series_weight_positive R 3%N n.
have[gamma [hSupport [hRange [hOne hDerivative]]]]:=@current_scaled_interval_cutoff_exists R h2
  (weighted_interval_left_endpoint R n) q hq.
exists gamma;split.
- rewrite weighted_interval_left_endpoint_step;exact:hSupport.
- split;first exact:hRange.
  split;first exact:hOne.
  move=>x;have h:=hDerivative x.
  by rewrite /q /reciprocal_power_series_weight exprVn invrK in h.
Qed.

(** Source for [weighted_interval_cutoff_family_exists]:
    a full family of the actual
    original phi_k exists, supporting Federer
    4.1.12, p. 369. *)
Theorem weighted_interval_cutoff_family_exists:
  exists f:nat->DT,@is_weighted_interval_cutoff_family R h2 f.
Proof. have[f hf]:=choice weighted_interval_cutoff_exists;by exists f. Qed.
End WeightedIntervalCutoffExistence.
