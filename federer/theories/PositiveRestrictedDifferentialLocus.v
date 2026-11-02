(** Federer (1969), 3.2.21, p. 257: the actual
    differentiability locus with positive restricted exterior power,
    intersected with the inverse image of the Borel target T. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology num_normedtype.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormMetric InnerOwnNormTopology NormDifferentialUP EuclideanLinearJacobian
  EuclideanSliceJacobianRepresentative EuclideanDifferentialObservables
  EuclideanLipschitzClassZero EuclideanHomOperator PartialFunctionUP PartialFunctionBasic
  LipschitzUP NormMetricScaleContinuity TopologicalBorel BorelFamilyBasic ContinuousBorelPreimages RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_restricted_differential_locus]: the
    set A after the orthogonal substitution in Federer 3.2.21,
    p. 257. Only actual differentials contribute; no
    default derivative is assigned elsewhere. The fixed block
    is an arbitrary linear map j. *)
Definition positive_restricted_differential_locus (R:realType) m n k
    (f:R_n R m->R_n R n) (j:Hom (R_n R k) (R_n R m))
    (T:set (R_n R n)):set (R_n R m):=
  [set x | T (f x) /\ exists D,
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D /\
    0<euclidean_linear_jacobian k (hom_comp D j)].

(** Source for [positive_restricted_differential_locus_borel]:
    Borel measurability needed for the Fubini selection in
    Federer 3.2.21, p. 257. The exact differential
    domain is Borel by 3.1.1 and its restricted Jacobian
    is continuous as a function of the differential. *)
Lemma positive_restricted_differential_locus_borel (R:realType) m n k
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (j:Hom (R_n R k) (R_n R m))
    (T:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_metric_lipschitz setT f ->borel_set T ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (positive_restricted_differential_locus f j T).
Proof.
move=>hLip hT.
pose h:=fun D:Hom (R_n R m) (R_n R n)=>euclidean_linear_jacobian k (hom_comp D j).
pose V:set (real_line_metric R):=fun r=>0<r.
have hV:open V.
  exact: open_gt.
have hObs:=euclidean_differential_observable_borel
  (euclidean_lipschitz_norm_class_zero hLip)
  (@euclidean_precomposed_top_jacobian_continuous R m n k j) (open_borel_set hV).
have hOwn:= (inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hObs.
have hPre:borel_set (f @^-1` T).
  apply:continuous_borel_preimage _ hT.
  have [L [hL hBound]]:=hLip.
  apply:(@metric_fixed_lipschitz_continuous R _ _ _ L (ltW hL))=>x y.
  exact:(hBound.2 x y Logic.I Logic.I).
have hEq:positive_restricted_differential_locus f j T=
    (f @^-1` T) `&` partial_function_preimage (euclidean_differential_observable f h) V.
  apply/seteqP; split=>x.
  - move=>[hTx [D [hD hJ]]]; split; first exact hTx.
    exists (h D); split; last exact hJ.
    apply:(euclidean_differential_observable_graph f h x _).2.
    exists D; by split.
  - move=>[hTx [r [hr hVr]]].
    have [D [hD hDr]]:=(euclidean_differential_observable_graph f h x r).1 hr.
    split; first exact hTx; exists D; split; first exact hD.
    change (is_true (0<h D)); by rewrite hDr.
rewrite hEq; exact: (borel_family_binary_intersection (borel_sets_family _) hPre hOwn).
Qed.
