(** Federer (1969), 3.2.22, p. 259: the
    factorization F composed psi=gamma composed phi on
    A_ij determines their actual differentials at full-density
    source points. No ambient equality is required. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialChain NormDifferentialLocal
  PartialFunctionUP EuclideanLebesgueDimensions CenteredBallRelations MeasureSetDensity
  EuclideanDifferentialsDensityAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_differential_factor_through_full_density_subset]:
    D(F composed psi_i)(a)=Dgamma_j(phi_ij(a)) composed
    Dphi_ij(a) in Federer 3.2.22, p. 259.
    Apply the actual chain rule to gamma composed phi,
    then use equality on the full-density source subset.
    Each actual differential is a proved premise at this
    supporting point; the global theorem supplies them by
    Rademacher and the all-points chart differential laws. *)
Lemma euclidean_differential_factor_through_full_density_subset (R:realType) m mu n
    (S:set (R_n R m)) (F:R_n R m->R_n R n)
    (phi:R_n R m->R_n R mu) (gamma:R_n R mu->R_n R n) a
    (H:Hom (R_n R m) (R_n R n)) (L:Hom (R_n R m) (R_n R mu))
    (D:Hom (R_n R mu) (R_n R n)):
  (forall x,S x ->F x=gamma (phi x)) ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R [the metricType R of
      inner_metric_space (@euclidean_inner_productP R m)]) (~` S)) a 0%E ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT F a H ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R mu)) setT phi a L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
    (inner_norm (@euclidean_inner_productP R n)) setT gamma (phi a) D ->
  H=hom_comp D L.
Proof.
move=>hAgree hDensity hF hPhi hGamma.
pose X:=R_n R m; pose U:=R_n R mu; pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NU:=inner_norm (@euclidean_inner_productP R mu).
pose NY:=inner_norm (@euclidean_inner_productP R n).
have hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
have hNU:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hChain:=@norm_differential_chain R X U Y NX NU NY hNX hNU hNY
  setT setT phi gamma a L D hPhi hGamma.
have hInterior:norm_domain_interior NX setT a.
  exists 1; split; first exact:ltr01; by move=>h hh.
have hWhole:=@norm_differential_restrict R X Y NX NY
  (fun x=>setT x /\ setT (phi x)) setT (fun x=>gamma (phi x)) a (hom_comp D L)
  (fun _ _=>conj Logic.I Logic.I) hInterior hChain.
exact:(@euclidean_differentials_agree_on_full_density R m Y NY hNY S F
  (fun x=>gamma (phi x)) a H (hom_comp D L) hAgree hDensity hF hWhole).
Qed.
