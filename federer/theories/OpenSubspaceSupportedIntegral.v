(** Federer (1969), 4.1.18, pp. 375–376:
    an ambient summable scalar function vanishing
    outside the original open U has exactly its
    original-U integral. Reuse 2.4.10's zero extension
    and 2.4.18's image integral, including empty U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric OpenSubspaceMeasure
  MeasureUP MeasureAlmostBasic MeasurePushforward MeasureRestriction
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialZeroExtension PartialZeroExtensionLaws
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  RestrictedIntegralIdentity RadonWeightedPushforwardIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_subspace_supported_total_integral]:
    the literal L1 convolution errors on U
    agree with their zero-extended ambient errors,
    supporting Federer 4.1.18, pp. 375–376.
    Signed and infinite integral values are retained. *)
Theorem open_subspace_supported_total_integral (R:realType)
    (X:pseudoMetricType R) (U:set X) (mu:set X->\bar R)
    (hm:is_measure mu) (hU:measure_measurable mu U) (g:X->R) a:
  (forall x,~U x->g x=0)->
  is_measure_integral mu (real_total_integrand g) a ->
  is_measure_integral (@open_subspace_measure R X U mu)
    (real_total_integrand (fun x:set_type U=>g (set_val x))) a.
Proof.
move=>hOff hIntegral.
have hZero:is_measure_integral mu
    (partial_function_zero_extension 0 U (real_total_integrand g)) a.
  apply:(@measure_integral_graph_equivalent R X mu _ _ a _ hIntegral)=>x y.
  case:(pselect (U x))=>hx.
  - by rewrite (partial_function_zero_extension_on _ _ _ hx).
  - rewrite (partial_function_zero_extension_off _ _ _ hx)
      real_total_integrand_graph (hOff x hx).
    change (0%E=y<->y=0%E);by split=>->.
have hRestricted: is_measure_integral (measure_restrict mu U)
    (real_total_integrand g) a.
  exact:((@restricted_integral_zero_extension_iff R X mu hm U
    (real_total_integrand g) a hU).2 hZero).
have hPull:is_measure_measurable_function (@open_subspace_measure R X U mu)
    (real_total_integrand (fun x:set_type U=>g (set_val x))).
  constructor.
  - have hDomain:partial_function_domain
        (real_total_integrand (fun x:set_type U=>g (set_val x)))=setT.
      apply:funext=>x;apply:propext;split;first by move=>_.
      move=>_;exists (g (set_val x))%:E.
      by apply/real_total_integrand_graph.
    rewrite hDomain;exact:measure_almost_everywhere_true
      (@open_subspace_measure_is_measure R X U mu hm).
  - move=>O hO.
    have hSet:(partial_function_preimage
        (real_total_integrand (fun x:set_type U=>g (set_val x))) O)=
        set_val @^-1` partial_function_preimage (real_total_integrand g) O.
      apply:funext=>x;apply:propext;split.
      - move=>[y [hY hYO]];exists y;by split.
      - move=>[y [hY hYO]];exists y;by split.
    rewrite hSet.
    exact:(@open_subspace_preimage_measurable R X U mu _
      (@measurable_function_open_preimage _ _ _ _ _ hIntegral.1 O hO)).
have hImage:is_measure_integral
    (measure_pushforward (set_val:set_type U->X) (@open_subspace_measure R X U mu))
    (real_total_integrand g) a.
  by rewrite open_subspace_measure_pushforward.
exact:((@real_total_pushforward_integral_iff R (set_type U) X
  (@open_subspace_measure R X U mu) (@open_subspace_measure_is_measure R X U mu hm)
  set_val g hPull a).2 hImage).
Qed.
