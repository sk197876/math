(** Federer (1969), 4.1.12, pp. 368–369: the
    original interval-current series converge in mass
    and define flat currents. Prove the supporting
    limit theorem in the actual complete flat space,
    then reuse the original weak mass lower-limit law
    to retain every quantitative mass-tail bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentPointEvaluation SmoothCompactSet
  CurrentSupportGeometry CurrentFlatNorm CurrentFlatMassComparison CurrentMassSealed NormalCurrentsUP
  FlatCurrentsUP FlatCurrentFinite FlatCurrentSpaces LinearSubspaceRepresentationUP
  NormVanishingTailIncrementLimit CurrentMassIncrementTails FlatCurrentConvergenceEvaluation CurrentMassWeakLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactNormalCurrentMassLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation W := (@flat_current_space R h2 n m U hU K).
Local Notation inc := (@flat_current_inclusion R h2 n m U hU K).
Local Notation hW := (@flat_current_space_laws R h2 n m U hU K).
Local Notation N := (@flat_current_norm R h2 n m U hU K).
Local Notation hN := (@flat_current_norm_is_norm R h2 n m U hU K).
Local Notation normalK := (@normal_currents_supported_in R h2 n U hU m K).
Local Notation support := (@current_support R h2 n U hU m).

(** Source for [compact_normal_current_mass_limit]:
    normal partial sums with one compact support
    and summable mass increments have an original
    flat limit T, with M(T-u_N)<=t_N and convergence
    on every original test. This proves existence,
    rather than assuming the current series in
    Federer 4.1.12, pp. 368–369. *)
Theorem compact_normal_current_mass_limit (u:nat->C) (t:nat->R):
  (forall k,normalK (u k))->
  (forall k,0<=t k)->
  (forall k,(M ((u k.+1-u k)%R)<=(t k-t k.+1)%:E)%E)->
  (forall epsilon:R,0<epsilon->exists k,t k<epsilon)->
  exists T:C,
    @is_flat_current_supported_in R h2 n m U hU K T /\
    (forall k,(M ((T-u k)%R)<=(t k)%:E)%E) /\
    forall phi:DT,forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
      `|action (u L) phi-action T phi|<epsilon.
Proof.
move=>hNormal hT hIncrement hSmall.
have hRepresent k:exists z:W,inc z=u k.
  have hFlat:=@supported_normal_current_is_flat R h2 n m U hU K (u k) (hNormal k).
  exact:(subspace_representation_full hW hFlat).
have [v hv]:=choice hRepresent.
have hNormIncrement k:N (v k.+1-v k)<=t k-t k.+1.
  have hImage:inc (v k.+1-v k)=u k.+1-u k.
    by rewrite (linB (hom_linear inc)) (hv k.+1) (hv k).
  have hValue:=@flat_current_norm_value R h2 n m U hU K (v k.+1-v k).
  rewrite hImage in hValue.
  have hSupport:support (u k.+1-u k) `<=` smooth_compact_carrier K.
    have h:=@current_support_linear_subset R h2 n m U hU K (-1) (u k) (u k.+1)
      (hNormal k).2 (hNormal k.+1).2.
    by rewrite scaleN1r addrC in h.
  have hFlatMass:=@current_flat_norm_le_mass R h2 n m U hU K (u k.+1-u k) hSupport.
  have h:=le_trans hFlatMass (hIncrement k).
  by rewrite hValue lee_fin in h.
have [z [hConvergence hNormTail]]:=@norm_vanishing_tail_increments_converge R W N hN
  (@flat_current_complete R h2 n m U hU K) v t hT hNormIncrement hSmall.
pose T:=inc z.
have hFlatT:@is_flat_current_supported_in R h2 n m U hU K T.
  exact:subspace_representation_member hW z.
have hWeak:forall phi:DT,forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    `|action (u L) phi-action T phi|<epsilon.
  move=>phi epsilon hEpsilon.
  have [k hk]:=@flat_current_convergence_evaluation R h2 n m U hU K v z hConvergence phi epsilon hEpsilon.
  exists k=>L hKL;have h:=hk L hKL;by rewrite (hv L) in h.
exists T;split;first exact:hFlatT.
split;last exact:hWeak.
move=>k.
pose Q L:=u L-u k.
pose Tail:=T-u k.
have hTailWeak:forall phi:DT,forall epsilon:R,0<epsilon->exists j,forall L,(j<=L)%N->
    `|action (Q L) phi-action Tail phi|<epsilon.
  move=>phi epsilon hEpsilon.
  have [j hj]:=hWeak phi epsilon hEpsilon.
  exists j=>L hJL.
  pose E:=@current_point_evaluation R h2 n m U hU phi.
  have hDifference:action (Q L) phi-action Tail phi=action (u L) phi-action T phi.
    change (E (u L-u k)-E (T-u k)=E (u L)-E T).
    rewrite !(linB (hom_linear E));ring.
  rewrite hDifference;exact:hj L hJL.
have hTailBound L (hKL:(k<=L)%N):(M (Q L)<=(t k)%:E)%E.
  exact:(@current_mass_increment_tail_bound R h2 n m U hU u t hT hIncrement k L hKL).
exact:(@current_mass_weak_closed_bound R h2 n m U hU Q Tail (t k)%:E k hTailWeak hTailBound).
Qed.
End CompactNormalCurrentMassLimit.
