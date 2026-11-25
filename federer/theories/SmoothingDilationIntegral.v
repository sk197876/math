(** Federer (1969), 4.1.2, p. 346: the
    original normalization survives every positive dilation.
    Exact measure pushforward and the existing scalar
    integral laws prove the displayed equality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanLebesgueDimensions MeasureUP MeasurePushforward MeasureScaleIntegral
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP SummableRealArithmetic InjectivePushforwardIntegral SmoothingKernelUP SmoothingDilationUP EuclideanDilationPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_dilation_integral_one]: every
    actual Phi_epsilon has original Lebesgue integral
    one, Federer 4.1.2, p. 346. *)
Theorem smoothing_dilation_integral_one (R:realType) n
    (phi:R_n R n->R) (family:R->R_n R n->R):
  is_smoothing_kernel phi ->is_smoothing_dilation phi family ->
  forall e:R,0<e ->is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (family e)) (1:R)%:E.
Proof.
move=>hPhi hFamily e he.
pose X:=R_n R n.
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
pose c:=e^+n.
have hc:0<c by rewrite /c; exact:exprn_gt0.
pose u:=fun x:X=>e^-1*:x.
have hCancel:cancel u (fun x:X=>e*:x).
  move=>x; by rewrite /u scalerA mulfV ?scale1r // gt_eqF.
have hInj:injective u:=can_inj hCancel.
have hScaled:=@measure_scale_integral R X mu hm c hc (real_total_integrand phi) (1:R)%:E
  (smoothing_kernel_integral_one hPhi).
rewrite mule1 in hScaled.
have hPush:=@euclidean_inverse_dilation_pushforward R n e he.
change (measure_pushforward u mu=measure_scale c mu) in hPush.
rewrite -hPush in hScaled.
have hPre:=(@injective_pushforward_integral_iff R X X mu hm u
  (real_total_integrand phi) hInj c%:E).2 hScaled.
have hIntegral:is_measure_integral mu (real_total_integrand (fun x=>phi (u x))) c%:E.
  apply:(@measure_integral_graph_equivalent R X mu _ _ c%:E _ hPre).
  move=>x y; change (partial_function_graph (real_total_integrand phi) (u x) y <->
    partial_function_graph (real_total_integrand (fun x=>phi (u x))) x y).
  by rewrite !real_total_integrand_graph.
have h:=@real_total_integral_scale R X mu hm (fun x=>phi (u x)) c c^-1 hIntegral.
have hC:c!=0 by rewrite (gt_eqF hc).
rewrite mulVf // in h.
have hEq:(fun x=>c^-1*phi (u x))=family e.
  apply:funext=>x; exact:esym (hFamily e he x).
by rewrite hEq in h.
Qed.
