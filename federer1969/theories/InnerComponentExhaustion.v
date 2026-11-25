(** Federer (1969), 4.1.4, pp. 348–349: the original
    inner components exhaust connected open A, and every
    compact subset lies in all sufficiently small components. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric CompactInverseSystemUP
  InnerParallelFamilyUP InnerParallelFamilyLaws InnerParallelFamilyOpen
  InnerComponentFamilyUP InnerComponentFamilyLaws
  DirectedOpenComponentExhaustion DirectedOpenCompactCapture.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section InnerComponentExhaustion.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation T := (real_norm_metric_space hNX).
Variable A:set X.
Hypothesis hA:@open T A.
Hypothesis hConnected:@connected T A.
Variable O:R->set X.
Hypothesis hO:is_inner_parallel_family NX A O.
Variable a:X.
Hypothesis ha:A a.
Variable C:R->set X.
Hypothesis hC:@is_inner_component_family R T O a C.

(** Source for [inner_component_exhausts_connected]: the
    components C_e cover the original connected A, the
    exhaustion inference used in Federer 4.1.4, p. 349. *)
Lemma inner_component_exhausts_connected:forall x,A x ->
  exists e:R,0<e /\ C e x.
Proof.
have hOpen:forall e:R,0<e ->@open T (O e).
  exact:(@inner_parallel_family_open R X NX hNX A O hO).
have hInside:forall e:R,0<e ->O e `<=` A.
  exact:(@inner_parallel_inside R X NX A O hO).
have hCover:forall x,A x ->exists e:R,0<e /\ O e x.
  move=>x hx.
  have[d [hd hSmall]]:=@inner_parallel_eventually_contains R X NX hNX A O hO hA x hx.
  have hd2:0<d/2 by lra.
  exists (d/2); split=>//; apply:(@hSmall (d/2) hd2); lra.
have hDirected:forall e d:R,0<e ->0<d ->exists k:R,
    0<k /\ (O e `<=` O k) /\ (O d `<=` O k).
  move=>e d he hd.
  have hk:0<Num.min e d by rewrite lt_min he hd.
  exists (Num.min e d); split=>//; split.
  - apply:(@inner_parallel_reverse_monotone R X NX A O hO _ e hk he).
    by rewrite ge_min lexx.
  - apply:(@inner_parallel_reverse_monotone R X NX A O hO _ d hk hd).
    by rewrite ge_min lexx orbT.
move=>x hx.
have[e [he hxe]]:=@directed_open_components_exhaust_connected R X NX hNX
  [the choiceType of R^o] (fun e:R=>0<e) A O hOpen hInside hCover hDirected a ha hConnected x hx.
exists e; split=>//; by rewrite (@hC e he).
Qed.

(** Source for [inner_component_eventually_contains_compact]:
    every compact support in A lies in C_e for all sufficiently
    small positive e, used in Federer 4.1.4, p. 349. *)
Theorem inner_component_eventually_contains_compact K:
  @compact T K ->K `<=` A ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->K `<=` C e.
Proof.
move=>hK hKA.
pose I:choiceType:=[the choiceType of {e:R|0<e}].
pose leI (e d:I):Prop:=(val d<=val e).
have hDirected:is_directed_preorder leI.
  constructor.
  - exists (Sub 1 (@ltr01 R)); by [].
  - by move=>e; rewrite /leI lexx.
  - move=>e d k hed hdk; exact:(le_trans hdk hed).
  - move=>e d.
    have hm:0<Num.min (val e) (val d) by rewrite lt_min (valP e) (valP d).
    exists (Sub (Num.min (val e) (val d)) hm); split.
    + by rewrite /leI /= ge_min lexx.
    + by rewrite /leI /= ge_min lexx orbT.
pose F (e:I):set T:=C (val e).
have hOpen:forall e:I,@open T (F e).
  move=>e; exact:(@inner_component_open R X NX hNX A O hO a C hC (val e) (valP e)).
have hMono:forall e d:I,leI e d ->F e `<=` F d.
  move=>e d hed.
  exact:(@inner_component_reverse_monotone R X NX hNX A O hO a C hC
    (val d) (val e) (valP d) (valP e) hed).
have hCover:forall x:T,K x ->exists e:I,F e x.
  move=>x hx.
  have[e [he hxe]]:=@inner_component_exhausts_connected x (hKA x hx).
  by exists (Sub e he).
have[d hCaptured]:=@directed_open_compact_capture T I leI hDirected F K hK hOpen hMono hCover.
exists (val d); split; first exact:(valP d).
move=>e he hed x hx.
apply:(@inner_component_reverse_monotone R X NX hNX A O hO a C hC
  e (val d) he (valP d) (ltW hed) x).
exact:(hCaptured x hx).
Qed.
End InnerComponentExhaustion.
