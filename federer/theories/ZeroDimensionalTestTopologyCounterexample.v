(** Federer (1969), 4.1.1, p. 344: concrete counterexample
    to the nonembedding sentence without a positive source
    dimension. Both spaces below are actual finite-dimensional
    Banach spaces; U is nonempty and Y is nonzero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness CompleteMetricUP
  EuclideanOwnNormCompleteness OpenFamilyTopologyUP SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothFunctionTopology
  SmoothTestSpaces SmoothTestTopology SmoothCompactDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ZeroDimensionalCounterexample.
Variable R:realType.
Local Notation X := (R_n R 0).
Local Notation Y := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R 1)).

(** Source for [zero_dimensional_source_singleton]: the entire
    zero-dimensional source is one point, supporting the missing
    exception in Federer 4.1.1, p. 344. *)
Lemma zero_dimensional_source_singleton (x:X):x=0.
Proof. apply/ffunP=>i; by have:=ltn_ord i; rewrite ltn0. Qed.

(** Source for [zero_dimensional_source_open]: the whole
    zero-dimensional source is open, supporting all original
    domain hypotheses of Federer 4.1.1, p. 343. *)
Lemma zero_dimensional_source_open x:
  (@setT X) x -> norm_domain_interior NX (@setT X) x.
Proof. move=>hx; exists 1; split; first exact:ltr01; by move=>v hv. Qed.

(** Source for [zero_dimensional_source_compact_index]: the
    nonempty entire domain is compact, supporting the concrete
    nonembedding correction to Federer 4.1.1, p. 344. *)
Definition zero_dimensional_source_compact_index:smooth_compact_set hNX (@setT X).
Proof.
refine (@Build_smooth_compact_set R X NX hNX (@setT X) setT _ _).
- by move=>x hx.
- have hEq:(@setT (real_norm_metric_space hNX))=[set (0:X)].
    apply:funext=>x; apply:propext; split=>hx; last exact:Logic.I.
    exact:zero_dimensional_source_singleton.
  rewrite hEq; exact:compact_set1.
Defined.

Local Notation E := (@SmoothFunctionSpace.space R X Y NX NY hNX hNY setT zero_dimensional_source_open).
Local Notation ev := (@SmoothFunctionSpace.value R X Y NX NY hNX hNY setT zero_dimensional_source_open).
Local Notation hE := (@SmoothFunctionSpace.laws R X Y NX NY hNX hNY setT zero_dimensional_source_open).
Local Notation D := (@SmoothFunctionDerivatives.operators R X Y NX NY hNX hNY setT E ev hE).
Local Notation hD := (@SmoothFunctionDerivatives.laws R X Y NX NY hNX hNY setT E ev hE).
Local Notation K := zero_dimensional_source_compact_index.

(** Source for [zero_dimensional_domain_covers]: the compact
    index contains every original domain point, supporting the
    correction to Federer 4.1.1, p. 344. *)
Lemma zero_dimensional_domain_covers x:
  (@setT X) x -> smooth_compact_carrier K x.
Proof. by []. Qed.

Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation EO := (smooth_function_opens hD).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation inv := (@smooth_compact_domain_inverse R X Y NX NY hNX hNY setT E ev hE
  K zero_dimensional_domain_covers).

(** Source for [zero_dimensional_test_topology_counterexample]:
    a nonempty U in the Banach space R^0 and nonzero Banach
    target R^1 have a homeomorphic D-to-E inclusion, refuting
    the unrestricted exception sentence in Federer 4.1.1,
    p. 344. Every original Banach hypothesis is retained. *)
Theorem zero_dimensional_test_topology_counterexample:
  is_complete_metric_space (real_norm_metric_space hNX) /\
  is_complete_metric_space (real_norm_metric_space hNY) /\
  (@setT X) 0 /\ (exists y:Y,y<>0) /\
  open_family_continuous SO EO inc /\ open_family_continuous EO SO inv /\
  cancel inv inc /\ cancel inc inv.
Proof.
split; first exact:euclidean_own_norm_complete.
split; first exact:euclidean_own_norm_complete.
split; first exact:Logic.I.
split.
- exists [ffun _: 'I_1=>(1:R)]=>hy.
  have h:=congr1 (fun y:Y=>y ord0) hy.
  have hBad:(1:R)=0 by move:h; rewrite !ffunE.
  by move:(oner_neq0 R); rewrite hBad eqxx.
- exact:(@smooth_compact_domain_homeomorphism R X Y NX NY hNX hNY setT E ev hE D hD
    K zero_dimensional_domain_covers).
Qed.
End ZeroDimensionalCounterexample.
