(** Federer (1969), 4.1.18, p. 377: the kernel
    of q is closed for J. This direction of the
    printed kernel-closure assertion follows from the
    exact density masses and the earlier mass-to-weak
    convergence laws. Compact carriers of the
    approximating pairs need not be uniform. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentMassSealed
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorLinear CurrentLonePairCost
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentPairMassKernelClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Kernel.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation P:=(@current_lone_pair_space R h2 n m U hU).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation D:=(@compact_summable_multivector_current R h2 n m U hU).
Local Notation E:=(@compact_summable_multivector_current R h2 n m.+1 U hU).
Local Notation DH:=(@compact_summable_multivector_current_hom R h2 n m U hU).
Local Notation EH:=(@compact_summable_multivector_current_hom R h2 n m.+1 U hU).
Local Notation sizeD:=(@compact_summable_multivector_size R h2 n m U hU).
Local Notation sizeE:=(@compact_summable_multivector_size R h2 n m.+1 U hU).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation NextM:=(@CurrentMass.value R h2 n m.+1 U hU).
Local Notation J:=(@current_lone_pair_cost R h2 n m U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).

(** Source for [current_lone_pair_map_kernel_closed]:
    J-limits of pairs in ker q remain in ker q,
    the closedness used in the final paragraph of
    Federer 4.1.18, p. 377. The input is
    any actual map satisfying the independent original
    q equation, not an assumed continuity theorem. *)
Theorem current_lone_pair_map_kernel_closed
    (Q:Hom P C) (hQ:@is_current_lone_pair_map R h2 n m U hU Q) (v:P):
  (forall epsilon:R,0<epsilon->exists w:P,
    Q w=0 /\J (v-w)<epsilon)->Q v=0.
Proof.
move=>hApprox;rewrite (hQ v).
apply:(@current_pair_mass_kernel_closed R h2 n m U hU (D v.1) (E v.2))
  =>epsilon hEpsilon.
have[w [hZero hCost]]:=hApprox epsilon hEpsilon.
exists (D w.1),(E w.2);split.
- by rewrite -(hQ w).
- have hFirst:M (D v.1-D w.1)=(sizeD (v.1-w.1))%:E.
    change (M (DH v.1-DH w.1)=(sizeD (v.1-w.1))%:E).
    rewrite -(linB (hom_linear DH) v.1 w.1).
    exact:(@compact_summable_multivector_current_mass R h2 n m U hU (v.1-w.1)).
  have hSecond:NextM (E v.2-E w.2)=(sizeE (v.2-w.2))%:E.
    change (NextM (EH v.2-EH w.2)=(sizeE (v.2-w.2))%:E).
    rewrite -(linB (hom_linear EH) v.2 w.2).
    exact:(@compact_summable_multivector_current_mass R h2 n m.+1 U hU (v.2-w.2)).
  rewrite hFirst hSecond -EFinD lte_fin.
  exact:hCost.
Qed.

(** Source for [current_lone_pair_kernel_closed]: the
    closedness assertion for the actual opaque original q,
    Federer 4.1.18, p. 377. Its existence and
    defining law are already proved. *)
Theorem current_lone_pair_kernel_closed (v:P):
  (forall epsilon:R,0<epsilon->exists w:P,
    @CurrentLonePair.map R h2 n m U hU w=0 /\J (v-w)<epsilon)->
  @CurrentLonePair.map R h2 n m U hU v=0.
Proof. exact:(@current_lone_pair_map_kernel_closed
  (@CurrentLonePair.map R h2 n m U hU)
  (@CurrentLonePair.laws R h2 n m U hU) v). Qed.
End Kernel.
