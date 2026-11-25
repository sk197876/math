(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    every ideal of the finite-dimensional holomorphic germ
    ring is a countable union of compact sets. The
    proved Noetherian theorem supplies the generators;
    the actual coefficient map supplies the compact images. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP RealNormUP LinearBasis HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric
  HolomorphicGermMultiplyContinuity HolomorphicGermNoetherian CommutativeIdealUP
  FiniteIdealCoefficientImage HolomorphicGermFiniteSumContinuity HolomorphicGermCompactCover
  ContinuousCommonPair IncreasingCompactCoverUP IncreasingCompactCoverLaws IncreasingCompactCoverProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_ideal_increasing_compact_cover_exists]:
    the exact ideal in the first paragraph of the
    proof of 3.4.8(5), p. 328, has a countable
    compact cover. Neither finite generators nor a compact
    ideal cover is an additional hypothesis. The original
    centre and zero-dimensional case remain. *)
Theorem holomorphic_ideal_increasing_compact_cover_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) a n (b:'I_n->X)
    (I:set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)):
  is_basis b ->is_commutative_ideal I ->
  exists K:nat->set (@holomorphic_germ_metric R X NX (complex_norm_real hNX) a),
    @is_increasing_compact_cover (@holomorphic_germ_metric R X NX (complex_norm_real hNX) a) I K.
Proof.
move=>hb hI.
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)].
pose M:=@holomorphic_germ_metric R X NX (complex_norm_real hNX) a.
have hNoetherian:=@finite_holomorphic_germ_ring_noetherian R X NX hNX n b a hb.
have [F hF]:=hNoetherian I hI.
pose P:=prod_topology (fun _:'I_(size F)=>M).
pose synthesis (c:P):M:=\sum_(i<size F) (c i:G)*nth 0 F i.
have hContinuous:continuous synthesis.
  apply:(@holomorphic_germ_finite_sum_continuous R X NX (complex_norm_real hNX) a P 'I_(size F)
    (fun i c=>(c i:G)*nth 0 F i))=>i.
  have hPair:=@continuous_common_domain_pair P M M (fun c=>c i)
    (fun _=>(nth 0 F i:M)) (@proj_continuous _ (fun _:'I_(size F)=>M) i) (@cst_continuous P M (nth 0 F i)).
  have hMultiply:=@holomorphic_germ_multiply_continuous R X NX (complex_norm_real hNX) a.
  move=>c U hU;exact:(hPair c _ (hMultiply (c i,nth 0 F i) U hU)).
have hImage:synthesis @` setT = I.
  apply/seteqP;split.
  - move=>x [c _ <-];apply:(@finite_ideal_coefficient_image G I F hF (synthesis c)).2.
    exists c;reflexivity.
  - move=>x hx.
    have [c hc]:=(@finite_ideal_coefficient_image G I F hF x).1 hx.
    exists c;first exact:Logic.I.
    exact:esym hc.
have [K hK]:=@holomorphic_germ_increasing_compact_cover_exists R X NX hNX a n b hb.
pose L j:set P:=fun c=>forall i,K j (c i).
have hL:@is_increasing_compact_cover P setT L.
  have hProduct:=@increasing_compact_cover_finite_product M setT K 'I_(size F) hK.
  have hWhole:[set c:P|forall i,setT (c i)]=setT.
    apply/seteqP;split=>c hc;first exact:Logic.I.
    by move=>i.
  by rewrite hWhole in hProduct.
exists (fun j=>synthesis @` L j).
have hResult:=@increasing_compact_cover_continuous_image P M setT L synthesis hL hContinuous.
by rewrite hImage in hResult.
Qed.
