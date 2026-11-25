(** Federer (1969), 4.1.18, pp. 374–375: retain
    the literal reflected weight Phi_epsilon(-z). Its
    positivity, compact support, smoothness and integral one
    follow from the public kernel/dilation laws and the
    already proved reflection invariance of Lebesgue measure.
    No evenness assumption is made.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormRegularity NormRegularityLinearMaps InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationSmooth SmoothingDilationIntegral SmoothingDilationNonzeroRadius
  EuclideanLebesgueDimensions EuclideanReflectionTranslation MeasureUP
  MeasurePushforward InjectivePushforwardIntegral PartialFunctionUP PartialFunctionPrecomposition
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingReflectedWeight.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation mu:=(@euclidean_lebesgue_measure R n).
Local Notation hm:=(euclidean_lebesgue_is_measure R n).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.

(** Source for [smoothing_reflected_weight]: the literal
    Phi_epsilon(-z) in both first displayed integrals
    and the deformation definition of 4.1.18, p. 374. *)
Definition smoothing_reflected_weight (z:X):R:=family epsilon (-z).
Local Notation w:=smoothing_reflected_weight.

(** Source for [smoothing_reflected_weight_nonnegative]: the
    original averaging weight of 4.1.18, p. 374,
    is nonnegative by the public 4.1.2 kernel laws. *)
Theorem smoothing_reflected_weight_nonnegative z:0<=w z.
Proof.
exact:(@smoothing_dilation_nonnegative R n phi hPhi family hFamily
  epsilon hEpsilon (-z)).
Qed.

(** Source for [smoothing_reflected_weight_radius]: every
    nonzero averaging weight satisfies |z|<epsilon,
    supporting the exact mass constant and support tube
    in 4.1.18, p. 375. *)
Theorem smoothing_reflected_weight_radius z:w z!=0->NX z<epsilon.
Proof.
move=>hz.
have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily
  epsilon hEpsilon (-z) hz.
by rewrite inner_normN in hRadius.
Qed.

(** Source for [smoothing_reflected_weight_off]: the
    reflected kernel vanishes beyond the original closed
    epsilon ball, supporting 4.1.18, pp. 374–375. *)
Theorem smoothing_reflected_weight_off z:epsilon<NX z->w z=0.
Proof.
move=>hz;apply:(@smoothing_dilation_zero_beyond_radius R n phi family
  hPhi hFamily epsilon hEpsilon (-z)).
by rewrite inner_normN.
Qed.

(** Source for [smoothing_reflected_weight_smooth]: reflection
    preserves the actual smooth kernel used in 4.1.18,
    p. 374; it does not identify reflected and
    unreflected values. *)
Theorem smoothing_reflected_weight_smooth:
  norm_class_all_orders hNX hNS (fun _=>True) w.
Proof.
pose L:Hom X X:= -(hom_of_linear (@linear_id R X)).
have hBound:norm_bounded_linear NX NX L.
  exists 1;split;first exact:ler01.
  move=>z;change (is_true (NX (-z)<=1*NX z));by rewrite inner_normN mul1r.
move=>k.
exact:(@norm_class_precompose_linear R X X R^o NX NX NS hNX hNX hNS
  (fun _=>True) (family epsilon) L k hBound
  (@smoothing_dilation_smooth R n phi hPhi family hFamily epsilon hEpsilon k)).
Qed.

(** Source for [smoothing_reflected_weight_integral_one]: the
    reflected weight has the same unit integral, used
    throughout 4.1.18, pp. 374–375. This follows
    from the actual measure pushforward under negation. *)
Theorem smoothing_reflected_weight_integral_one:
  is_measure_integral mu (real_total_integrand w) (1:R)%:E.
Proof.
have hReflection:measure_pushforward (fun z:X=>-z) mu=mu.
  have h:=@euclidean_reflection_translation_measure R n (0:X).
  have hMap:(fun z:X=>(0:X)-z)=(fun z:X=>-z).
    apply:funext=>z;by rewrite sub0r.
  by rewrite hMap in h.
have hOriginal:=@smoothing_dilation_integral_one R n phi family hPhi hFamily
  epsilon hEpsilon.
rewrite -hReflection in hOriginal.
have hPre:=(@injective_pushforward_integral_iff R X X mu hm (fun z:X=>-z)
  (real_total_integrand (family epsilon)) (@oppr_inj X) (1:R)%:E).2 hOriginal.
apply:(@measure_integral_graph_equivalent R X mu _ _ (1:R)%:E _ hPre).
move=>z a;change (partial_function_graph (real_total_integrand (family epsilon)) (-z) a <->
  partial_function_graph (real_total_integrand w) z a).
by rewrite !real_total_integrand_graph.
Qed.
End SmoothingReflectedWeight.
