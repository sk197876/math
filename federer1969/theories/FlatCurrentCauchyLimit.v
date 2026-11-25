(** Federer (1969), 4.1.14, p. 370: the original
    F_E Cauchy sequence has an actual flat-current limit.
    Use completeness of the already specified opaque flat
    space from 4.1.12, p. 368, with its exact inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm FlatCurrentsUP FlatCurrentClosure FlatCurrentSpaces
  LinearSubspaceRepresentationUP CompleteMetricUP CurrentFlatSequenceLimitUP
  CurrentFlatSequenceLimits CurrentFlatSequenceComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentCauchyLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation W:=(@flat_current_space R h2 n m U hU K).
Local Notation Norm:=(@flat_current_norm R h2 n m U hU K).
Local Notation hNorm:=(@flat_current_norm_is_norm R h2 n m U hU K).
Local Notation inc:=(@flat_current_inclusion R h2 n m U hU K).
Local Notation hW:=(@flat_current_space_laws R h2 n m U hU K).
Local Notation flatK:=(@is_flat_current_supported_in R h2 n m U hU K).
Local Notation Cauchy:=(@is_current_flat_cauchy_sequence R h2 n m U hU K).
Local Notation Limit:=(@is_current_flat_sequence_limit R h2 n m U hU K).

(** Source for [flat_current_cauchy_sequence_limit]: the original
    complete F_(m,E)(V) supplies an actual limit of every
    F_E Cauchy sequence in that space, Federer 4.1.14,
    p. 370. The chosen carrier representatives occur only
    in this existence proof. *)
Theorem flat_current_cauchy_sequence_limit (u:nat->C):
  (forall i,flatK (u i))->Cauchy u->
  exists T:C,flatK T /\Limit u T.
Proof.
move=>hFlat hCauchy.
have hRepresentative i:exists z:W,inc z=u i.
  exact:(@subspace_representation_full R C W
    (@flat_current_subspace R h2 n m U hU K) inc hW (u i) (hFlat i)).
have[v hv]:=choice hRepresentative.
have hC:cauchy ((fun i=>(v i:real_norm_metric_space hNorm)) @ \oo).
  apply:cauchy_exP=>epsilon hEpsilon.
  have[k hk]:=hCauchy epsilon hEpsilon.
  exists (v k:real_norm_metric_space hNorm);exists k=>// i hKi.
  rewrite ballEmdist /=.
  change (is_true (Norm (v k-v i)<epsilon)).
  have h:=hk k i (leqnn k) hKi.
  rewrite -(hv k) -(hv i) -(linB (hom_linear inc))
    flat_current_norm_value lte_fin in h.
  exact:h.
have hProperNat:ProperFilter (\oo:set_system nat) by typeclasses eauto.
have hProper:ProperFilter ((fun i=>(v i:real_norm_metric_space hNorm)) @ \oo):=
  @fmap_proper_filter nat (real_norm_metric_space hNorm) v \oo hProperNat.
pose hComplete:=@flat_current_complete R h2 n m U hU K.
have[z hz]:=@hComplete _ hProper hC.
exists (inc z);split;first exact:subspace_representation_member hW z.
have hLimit:=@flat_current_norm_sequence_limit R h2 n m U hU K v z hz.
have hValues:(fun i=>inc (v i))=u by apply:funext=>i;exact:hv i.
by rewrite hValues in hLimit.
Qed.

(** Source for [flat_current_eventual_cauchy_sequence_limit]:
    only sufficiently late smooth images need lie in E,
    as in Federer 4.1.14, p. 370. Completeness is applied
    to that tail, and the original full sequence has the same
    actual limit; the finite prefix is unrestricted. *)
Theorem flat_current_eventual_cauchy_sequence_limit (u:nat->C) k:
  (forall i,(k<=i)%N->flatK (u i))->Cauchy u->
  exists T:C,flatK T /\Limit u T.
Proof.
move=>hFlat hCauchy.
have hTailFlat i:flatK (u (k+i)%N):=hFlat _ (leq_addr i k).
have hTailCauchy:Cauchy (fun i=>u (k+i)%N).
  move=>epsilon hEpsilon;have[N hN]:=hCauchy epsilon hEpsilon.
  exists N=>i j hNi hNj.
  exact:hN _ _ (leq_trans hNi (leq_addl k i))
    (leq_trans hNj (leq_addl k j)).
have[T [hT hLimit]]:=flat_current_cauchy_sequence_limit hTailFlat hTailCauchy.
exists T;split;first exact:hT.
exact:current_flat_sequence_limit_of_tail hLimit.
Qed.
End FlatCurrentCauchyLimit.
