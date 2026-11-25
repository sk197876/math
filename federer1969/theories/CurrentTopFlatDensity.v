(** Federer (1969), 4.1.18, p. 376, final
    paragraph: F_n(U) consists exactly of the Lebesgue
    currents of compactly supported summable n-vectorfields.
    The next-degree coefficient is actually zero by 1.3.2;
    finite mass is a consequence, never a premise. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary FlatCurrentsUP CurrentCompactClosedTubeInside
  CurrentFlatLonePairRepresentation CompactSummableMultivectors
  CompactSummableMultivectorAboveDimension CompactSummableMultivectorDensity
  CompactSummableMultivectorLinear CurrentLonePairImageUP CurrentLonePairImageSealed
  CurrentLonePairGlobalFlat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TopDegree.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation W:=(@compact_summable_multivector_space R h2 n n U hU).
Local Notation D:=(@compact_summable_multivector_current_hom R h2 n n U hU).
Local Notation Dnext:=(@compact_summable_multivector_current_hom R h2 n n.+1 U hU).
Local Notation bd:=(@current_boundary R h2 n n U hU).

(** Source for [current_top_flat_density]: the exact
    top-degree characterization in Federer 4.1.18,
    p. 376. The current is arbitrary on both
    sides; no representation, mass or normality assumption
    is added. Empty U and R^0 are included. *)
Theorem current_top_flat_density (T:@current_space R h2 n U hU n):
  @is_flat_current R h2 n n U hU T <->exists xi:W,T=D xi.
Proof.
split.
- move=>[K hFlat].
  have[delta [hDelta hInside]]:=@current_compact_closed_tube_inside_exists R n U hU K.
  have[v [hValue _]]:=@current_flat_lone_pair_representation R h2 n n U hU
    K T delta hFlat hDelta hInside.
  have hNext:v.2=0:=@compact_summable_multivector_above_dimension R h2 n n.+1
    (ltnSn n) U hU v.2.
  rewrite (@CurrentLonePair.laws R h2 n n U hU v) hNext in hValue.
  change (D v.1+bd (Dnext 0)=T) in hValue.
  rewrite !linear0 addr0 in hValue.
  exists v.1;exact:esym hValue.
- move=>[xi ->].
  have hFlat:=@current_lone_pair_is_flat R h2 n n U hU (xi,0).
  rewrite (@CurrentLonePair.laws R h2 n n U hU (xi,0)) /= in hFlat.
  change (@is_flat_current R h2 n n U hU (D xi+bd (Dnext 0))) in hFlat.
  by rewrite !linear0 addr0 in hFlat.
Qed.
End TopDegree.
