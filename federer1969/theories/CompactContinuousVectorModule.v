(** Federer (1969), 4.1.5, p. 349: the actual compact
    continuous fields satisfy every vector lattice module
    clause required by 2.5.12. The previous continuous
    radial split and scalar support theorems supply the
    assertions, including their zero-vector boundaries. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity
  FunctionLatticeUP CompactSupportFunctionUP CompactSupportFunctionLattice
  VectorDaniellHypotheses VectorDaniellDualExtension ContinuousRadialSplitLaws ContinuousRadialSplit
  CompactContinuousVectorFields CompactContinuousVectorSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_vector_lattice_module]:
    scalar products, dual pairings, norms and the exact
    radial split hold for the original D in Federer 4.1.5,
    p. 349. These are proved premises of the subsequent
    representation theorem, not additional hypotheses. *)
Theorem compact_continuous_vector_lattice_module (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY):
  is_vector_lattice_module hNY (@compactly_supported_continuous_functions R X)
    (@compact_continuous_vector_fields R X Y NY hNY).
Proof.
constructor.
- move=>f y hf; split.
  + change (continuous ((fun x:X=>f x*:y):X->real_norm_metric_space hNY)).
    move=>x.
    have hF:continuous (f:X->real_line_metric R):=hf.1.
    have hOrbit:continuous (fun c:real_line_metric R=>(c*:y:real_norm_metric_space hNY)):=
      @real_norm_metric_scalar_orbit_continuous R Y NY hNY y.
    exact:continuous_comp (hF x) (hOrbit (f x)).
  + apply:(@compact_support_unary_operation R X f (fun x=>NY (f x*:y)) hf.2)=>x hx.
    by rewrite hx scale0r (real_seminorm_zero hNY.1).
- move=>w alpha hw hAlpha; split.
  + move=>x; exact:continuous_comp (hw.1 x) (hAlpha.2 (w x)).
  + apply:(@compact_support_unary_operation R X (fun x=>NY (w x)) (fun x=>alpha (w x)) hw.2)=>x hx.
    by rewrite (hNY.2 _ hx) (@dual_space_zero R Y NY hNY alpha hAlpha).
- move=>w hw; exact:(@compact_continuous_vector_field_norm R X Y NY hNY w hw).
- move=>w f hw hf hBound.
  exists (fun x=>norm_radial_split NY (w x) (f x)); split.
  + split.
    * exact:(@norm_radial_split_continuous R X Y NY hNY w f hw.1 hf.1.1 hf.2 hBound).
    * have hNorm:(fun x=>NY (norm_radial_split NY (w x) (f x)))=f.
        apply:funext=>x; exact:(@norm_radial_split_norm R Y NY hNY (w x) (f x) (hf.2 x) (hBound x)).
      by rewrite hNorm; exact:hf.1.2.
  + split.
    * move=>x; exact:(@norm_radial_split_norm R Y NY hNY (w x) (f x) (hf.2 x) (hBound x)).
    * move=>x; exact:(@norm_radial_split_product R Y NY hNY (w x) (f x)).
Qed.
