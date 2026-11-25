(** Federer (1969), 4.1.18, pp. 375–377: the
    opaque pair map preserves the original current value,
    and its fibres are exactly the cosets of the original
    kernel. Together with surjectivity this is the original
    quotient presentation, without constructing a second carrier. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CompactSummableMultivectorDensity
  CurrentLonePairImageUP CurrentLonePairImageSealed
  FlatCurrentUnionSpace CurrentLonePairFlatUP CurrentLonePairFlatSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FlatPairLaws.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation P:=(@current_lone_pair_space R h2 n m U hU).
Local Notation Q:=(@CurrentLonePairFlat.map R h2 n m U hU).
Local Notation inc:=(@flat_current_union_inclusion R h2 n m U hU).
Local Notation q:=(@CurrentLonePair.map R h2 n m U hU).

(** Source for [current_lone_pair_flat_value]: actual flat
    inclusion gives exactly the original q value,
    Federer 4.1.18, p. 375. *)
Theorem current_lone_pair_flat_value (v:P):inc (Q v)=q v.
Proof. exact:(@CurrentLonePairFlat.laws R h2 n m U hU v). Qed.

(** Source for [current_lone_pair_flat_current_formula]: the
    flat-valued map has exactly the original two summands,
    Federer 4.1.18, p. 375. *)
Theorem current_lone_pair_flat_current_formula (v:P):
  inc (Q v)=@compact_summable_multivector_current R h2 n m U hU v.1+
    @current_boundary R h2 n m U hU
      (@compact_summable_multivector_current R h2 n m.+1 U hU v.2).
Proof. rewrite current_lone_pair_flat_value;exact:CurrentLonePair.laws. Qed.

(** Source for [current_lone_pair_flat_quotient_fibres]: two
    original pairs have the same quotient value exactly
    when their difference belongs to the actual kernel,
    Federer 4.1.18, pp. 375–377. *)
Theorem current_lone_pair_flat_quotient_fibres (v w:P):
  Q v=Q w <->q (v-w)=0.
Proof.
split.
- move=>hEqual.
  have h:=congr1 inc hEqual.
  rewrite !current_lone_pair_flat_value in h.
  by rewrite (linB (hom_linear q)) h subrr.
- move=>hKernel.
  apply:(@flat_current_union_inclusion_injective R h2 n m U hU).
  rewrite !current_lone_pair_flat_value.
  apply/eqP;rewrite -subr_eq0;apply/eqP.
  by rewrite -(linB (hom_linear q)).
Qed.
End FlatPairLaws.
