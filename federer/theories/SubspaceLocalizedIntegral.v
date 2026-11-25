(** Federer (1969), 4.1.5, p. 350:
    a compact localization of the original
    measure has the same small-ball integrals
    inside that compact neighbourhood. This is
    the exact image and restriction law of
    2.4.10 and 2.4.18, pp. 85, 90–91. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureRestriction MeasurePushforward MeasureSubsetIntegral MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasurableFunctionUP PushforwardMeasurabilityTransfer
  PushforwardIntegral RestrictedIntegralIdentity SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SubspaceLocalizedIntegral.
Variable R:realType.
Variable T:choiceType.
Variable U:set T.
Local Notation X := (set_type U).
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Variable K:set X.
Local Notation inclusion := (fun x:X=>(set_val x:T)).
Local Notation nu := (measure_pushforward inclusion (measure_restrict mu K)).

(** Source for [subspace_localized_mass]: the localized
    measure equals the original measure on
    sets lying in its compact piece,
    supporting Federer 4.1.5, p. 350. *)
Lemma subspace_localized_mass (A:set T):
  inclusion @^-1` A `<=` K ->nu A=mu (inclusion @^-1` A).
Proof.
move=>hA; rewrite /measure_pushforward /measure_restrict.
congr mu; apply/seteqP; split; first by move=>x [_ hx].
by move=>x hx; split=>//; exact:hA.
Qed.

(** Source for [subspace_localized_subset_integral]: the
    original and localized scalar integrals
    coincide on every small ball inside the
    compact piece, Federer 4.1.5, p. 350.
    Exact partial restriction graphs are retained. *)
Theorem subspace_localized_subset_integral (f:X->R) (g:T->R) (A:set T) (z: \bar R):
  measure_measurable mu K ->(forall x,g (inclusion x)=f x) ->
  inclusion @^-1` A `<=` K ->
  is_measure_subset_integral nu A (real_total_integrand g) z ->
  is_measure_subset_integral mu (inclusion @^-1` A) (real_total_integrand f) z.
Proof.
move=>hK hValues hA hIntegral.
have hRestricted:=measure_restrict_is_measure hm K.
pose p:=partial_function_zero_extension 0 A (real_total_integrand g).
have hMeasurable:=@measurable_function_pushforward_precompose R X T (extended_real_line R)
  inclusion (measure_restrict mu K) p (@val_inj _ _ _) hIntegral.1.
have hPre:=(@measure_pushforward_integral_iff R X T (measure_restrict mu K) hRestricted
  inclusion p hMeasurable z).2 hIntegral.
have hLocal:is_measure_subset_integral (measure_restrict mu K) (inclusion @^-1` A)
    (real_total_integrand f) z.
  apply:(@measure_integral_graph_equivalent R X (measure_restrict mu K) _ _ _ _ hPre)=>x q.
  rewrite /p /partial_function_precompose /= !partial_function_zero_extension_graph
    !real_total_integrand_graph hValues.
  reflexivity.
have hDouble:=(@restricted_integral_zero_extension_iff R X mu hm K _ z hK).1 hLocal.
have hIntersection:K `&` (inclusion @^-1` A)=inclusion @^-1` A.
  apply/seteqP; split; first by move=>x [_ hx].
  by move=>x hx; split=>//; exact:hA.
apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hDouble)=>x q.
by rewrite partial_zero_extension_intersection_graph hIntersection.
Qed.
End SubspaceLocalizedIntegral.
