(** Federer (1969), 4.1.18, p. 375: independent
    specification of the original positive average of
    translated Radon measures. Its scalar compact-test
    formula is literal; no construction or symmetry
    of the kernel is part of the specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain EuclideanLebesgueDimensions
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP RadonCompactScalarIntegral RadonPositiveCompactComparison
  FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanKernelRadonAverageUP.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation XT:=(real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n))).
Local Notation FT:=(current_domain R n (fun _=>True)).
Variable beta:set FT->\bar R.
Hypotheses (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta).
Variable w:X->R.
Local Notation D:=(@radon_positive_compact_integral R FT beta hBeta hBetaRadon).

(** Source for [is_euclidean_kernel_radon_average]:
    the original Radon average in Federer 4.1.18,
    p. 375, specified by its positive compact
    test integrals. Each inner integral is against
    the original measure and its literal translation. *)
Definition is_euclidean_kernel_radon_average (nu:set XT->\bar R):Prop:=
  is_measure nu /\is_radon_measure nu /\
  forall (hNu:is_measure nu) (hNuRadon:is_radon_measure nu) (f:XT->R),
    positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (fun z:X=>w z*D (fun x:FT=>f (set_val x+z))))
      (@radon_positive_compact_integral R XT nu hNu hNuRadon f)%:E.

(** Source for [euclidean_kernel_radon_average_unique]:
    the original compact scalar integral formula
    determines every outer measure, by 2.5.14 and
    Radon regularity, supporting the opaque measure
    of Federer 4.1.18, p. 375. *)
Theorem euclidean_kernel_radon_average_unique (mu nu:set XT->\bar R):
  is_euclidean_kernel_radon_average mu ->
  is_euclidean_kernel_radon_average nu ->mu= nu.
Proof.
move=>[hm [hr hM]] [hn [hs hN]].
pose F:=@radon_positive_compact_integral R XT mu hm hr.
pose G:=@radon_positive_compact_integral R XT nu hn hs.
have hEqual f (hF:positive_function_lattice (@compactly_supported_continuous_functions R XT) f):
    F f= G f.
  exact:(EFin_inj (measure_integral_unique (@hM hm hr f hF) (@hN hn hs f hF))).
have hOrder f (hF:positive_function_lattice (@compactly_supported_continuous_functions R XT) f):
    F f<=G f by rewrite (hEqual f hF).
have hReverse f (hF:positive_function_lattice (@compactly_supported_continuous_functions R XT) f):
    G f<=F f by rewrite (hEqual f hF).
have hForward:=@radon_positive_compact_integral_comparison R XT mu nu hm hn hr hs F G
  (@radon_positive_compact_integral_laws R XT mu hm hr)
  (@radon_positive_compact_integral_laws R XT nu hn hs)
  hOrder.
have hBackward:=@radon_positive_compact_integral_comparison R XT nu mu hn hm hs hr G F
  (@radon_positive_compact_integral_laws R XT nu hn hs)
  (@radon_positive_compact_integral_laws R XT mu hm hr)
  hReverse.
apply:funext=>A;apply/eqP;by rewrite eq_le (hForward A) (hBackward A).
Qed.
End EuclideanKernelRadonAverageUP.
Arguments is_euclidean_kernel_radon_average : clear implicits.
