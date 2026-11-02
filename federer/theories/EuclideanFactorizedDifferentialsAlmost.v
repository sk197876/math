(** Federer (1969), 3.2.22, p. 259: the
    actual differential factorization on almost every point
    of each measurable chart-pair parameter set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP LipschitzUP Rademacher EuclideanLebesgueDimensions
  MeasureUP MeasureAlmostUP MeasureAlmostBasic EuclideanFullDensityCore
  RectifiableCompactChartsUP EuclideanDifferentialFactorThroughSubset.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_factorized_differentials_almost]:
    D(F composed psi_i)=Dgamma_j(phi_ij) composed Dphi_ij
    for Lebesgue-almost every point of A_ij, Federer
    3.2.22, p. 259. A full-density core and
    two applications of Rademacher supply the actual source
    differentials; the target chart supplies its actual
    differential at every point of C_j. No differentiability
    of an arbitrary extension is inferred from agreement alone. *)
Theorem euclidean_factorized_differentials_almost (R:realType) m mu n
    (lambda:R) (A:set (R_n R m)) (C:set (R_n R mu))
    (F:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (phi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R mu))
    (gamma:R_n R mu->R_n R n):
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_metric_lipschitz setT F ->is_metric_lipschitz setT phi ->
  is_uniform_compact_rectifiable_chart lambda C gamma ->
  (forall a,A a ->C (phi a) /\ F a=gamma (phi a)) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A [set a|
    exists (H:Hom (R_n R m) (R_n R n)) (L:Hom (R_n R m) (R_n R mu))
      (D:Hom (R_n R mu) (R_n R n)),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT F a H /\
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R mu)) setT phi a L /\
      has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
        (inner_norm (@euclidean_inner_productP R n)) setT gamma (phi a) D /\
      H=hom_comp D L /\
      forall v,lambda^-1*inner_norm (@euclidean_inner_productP R mu) v<=
        inner_norm (@euclidean_inner_productP R n) (D v) /\
        inner_norm (@euclidean_inner_productP R n) (D v)<=
          lambda*inner_norm (@euclidean_inner_productP R mu) v].
Proof.
move=>hA hF hPhi hChart hAgreement.
pose hm:=euclidean_lebesgue_is_measure R m.
have [S [hSA [hNull hFull]]]:=euclidean_full_density_core_exists hA.
have hCore:measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A S:=hNull.
have hBoth:=measure_almost_everywhere_and hm
  ((measure_almost_everywhere_on_implication _ _ _).1 hCore)
  (measure_almost_everywhere_and hm (federer_3_1_6 hF) (federer_3_1_6 hPhi)).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hm _ hBoth)=>a [hCoreA [[H hH] [L hL]]] ha.
have hSa:S a:=hCoreA ha.
have [D [hD hBounds]]:=rectifiable_chart_differential_bounds hChart (hAgreement a ha).1.
have hEq:=@euclidean_differential_factor_through_full_density_subset R m mu n
  S F phi gamma a H L D (fun x hx=>(hAgreement x (hSA x hx)).2)
  (hFull a hSa) hH hL hD.
exists H,L,D; split; first exact hH; split; first exact hL.
split; first exact hD; by split.
Qed.
