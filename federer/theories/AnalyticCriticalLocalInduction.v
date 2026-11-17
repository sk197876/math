(** Federer (1969), 3.4.8(11), p. 333:
    induction on the smaller critical-germ dimension
    gives a neighbourhood of every centre meeting
    finitely many components of H. Translate its
    actual equations to zero and transfer the
    component count through the actual inverse translation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies NormDifferentialUP NormClosureLaws SetGermUP
  FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed AnalyticSourceTranslation
  AnalyticCriticalCentreDepth EmptyGermLocalComponents LocalComponentInverseTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CriticalInduction.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n.+1->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n.+1->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n.+1 e he omega).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).

(** Source for [analytic_critical_local_finiteness_from_induction]:
    the local component conclusion for H
    in 3.4.8(11), p. 333. The
    lower-depth induction input is explicit; the
    original critical dimension drop and translations
    are proved, not supplied as numbered-theorem premises. *)
Theorem analytic_critical_local_finiteness_from_induction (A:set X) (f:X->R^o) (D:X->Hom X R^o):
  @is_finite_analytic_variety R X NX hNX A [set x|A x /\ forall v,D x v = 0] ->
  (forall x,A x ->has_norm_differential NX (fun z:R^o=>`|z|) A f x (D x)) ->
  (forall a,A a ->~(exists r:R,0<r /\ forall x,NX (x-a)<r ->A x /\ f x = f a)) ->
  (forall W L:set X,W 0 ->@is_finite_analytic_variety R X NX hNX W L ->
    germ L<>germ set0 ->(depth (ideal (germ L))<n.+1)%N ->
    exists U:set X,@open T U /\ U 0 /\
      finite_set (@connected_component T L @` (L `&` U))) ->
  forall a,A a ->exists U:set X,@open T U /\ U a /\
    finite_set (@connected_component T [set x|A x /\ forall v,D x v = 0] @`
      ([set x|A x /\ forall v,D x v = 0] `&` U)).
Proof.
move=>hVariety hD hNotConstant hInduction a ha.
pose H:set X:=[set x|A x /\ forall v,D x v = 0].
pose A':set X:=[set y|A (a+y)].
pose H':set X:=[set y|H (a+y)].
have hA0:A' 0 by change (A (a+0));rewrite addr0.
have hH':@is_finite_analytic_variety R X NX hNX A' H'.
  exact:finite_analytic_variety_source_translation hVariety.
have hDrop:=@analytic_critical_centre_depth_drop R X B hB n e he hON omega hDual
  A f D a ha hVariety hD (hNotConstant a ha).
have hLocal:exists U:set X,@open T U /\ U 0 /\
    finite_set (@connected_component T H' @` (H' `&` U)).
  case:hDrop=>[hEmpty|hSmaller].
  - exact:(@empty_germ_local_component_finiteness T 0 H' hEmpty).
  - case:(pselect (germ H' = germ set0))=>hEmpty.
    + exact:(@empty_germ_local_component_finiteness T 0 H' hEmpty).
    + exact:hInduction A' H' hA0 hH' hEmpty hSmaller.
have [U [hU [hU0 hFinite]]]:=hLocal.
pose u:=fun x:T=>(a+x:T).
pose v:=fun x:T=>(x-a:T).
have hUMap:continuous u:=@real_norm_metric_translate_continuous R X NX hNX a.
have hVMap:continuous v.
  have hSame:v = (fun x:T=>(-a+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hVU:cancel u v by move=>x;rewrite /u /v addrAC subrr add0r.
have hUV:cancel v u by move=>x;rewrite /u /v addrC subrK.
exists (v @^-1` U);split.
- exact:(@open_comp T T v U (fun x _=>hVMap x) hU).
split;first by change (U (a-a));rewrite subrr.
exact:(@local_component_inverse_transport T T u v H U hUMap hVMap hVU hUV hFinite).
Qed.
End CriticalInduction.
