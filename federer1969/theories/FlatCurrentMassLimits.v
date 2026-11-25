(** Federer (1969), 4.1.17, p. 374: pass from smooth
    coefficient contractions to the original variation-summable
    coefficient by mass approximation in one fixed compact index.
    Reuse the original finite-flat norm, weak support preservation
    and F_K<=M from 4.1.12, pp. 367–368. No mass or support
    hypothesis is added to the candidate limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentSupportGeometry
  LinearSubspaceRepresentationUP CurrentFiniteFlatSpace CurrentFiniteFlatOperator
  CurrentFiniteFlatCompleteness CurrentFlatNorm CurrentFlatDualSeminormBasic
  CurrentFlatFiniteArithmetic
  CurrentFlatMassComparison CurrentMassSealed FlatCurrentsUP FlatCurrentFinite
  CurrentMassWeakConvergence CurrentWeakLimitOperations GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentMassLimits.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU K).
Local Notation support := (@current_support R h2 n U hU m).

(** Source for [current_finite_flat_add_bound]: the triangle
    inequality for the original finite F_K norm, already proved
    on the actual opaque finite-flat space in 4.1.12, p. 367;
    supporting the closure step in Federer 4.1.17, p. 374.
    Reuse that norm through its exact original-current inclusion. *)
Lemma current_finite_flat_add_bound (T S:C):
  (F T< +oo)%E->(F S< +oo)%E->(F (T+S)<=F T+F S)%E.
Proof. exact:(@current_flat_finite_triangle R h2 n m U hU K T S). Qed.

(** Source for [flat_current_flat_approximation_closed]: the
    original F_K closure of supported normal currents is itself
    closed under arbitrarily accurate F_K approximation by its
    members, by 4.1.12, p. 368; supporting the limiting argument
    in Federer 4.1.17, p. 374. The candidate current need not
    be assumed supported in K or have finite mass. *)
Theorem flat_current_flat_approximation_closed (T:C):
  (forall epsilon:R,0<epsilon->exists S:C,
    flatK S /\(F (T-S)<epsilon%:E)%E)->flatK T.
Proof.
move=>hApprox epsilon hEpsilon.
have hHalf:0<epsilon/2 by rewrite divr_gt0 // ltr0n.
have[S [hFlatS hFirst]]:=hApprox (epsilon/2) hHalf.
have[Q [hNormalQ hSecond]]:=hFlatS (epsilon/2) hHalf.
have hFirstFinite:(F (T-S)< +oo)%E:=lt_trans hFirst (ltry _).
have hSecondFinite:(F (S-Q)< +oo)%E:=lt_trans hSecond (ltry _).
have[a [ha hA]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m (T-S)) hFirstFinite.
have[b [hb hB]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m (S-Q)) hSecondFinite.
change (F (T-S)=a%:E) in hA.
change (F (S-Q)=b%:E) in hB.
have hRealFirst:a<epsilon/2 by move:hFirst;rewrite hA lte_fin.
have hRealSecond:b<epsilon/2 by move:hSecond;rewrite hB lte_fin.
have hSum:=current_finite_flat_add_bound hFirstFinite hSecondFinite.
have hIdentity:(T-S)+(S-Q)=T-Q by rewrite addrA subrK.
rewrite hIdentity hA hB -EFinD in hSum.
exists Q;split;first exact:hNormalQ.
apply:(le_lt_trans hSum);rewrite lte_fin;lra.
Qed.

(** Source for [flat_current_mass_approximation_support]: mass
    approximation by flat currents in the same compact index
    preserves the original support constraint, by the preceding
    mass-to-weak convergence and weak support laws of 4.1.12,
    p. 368; supporting Federer 4.1.17, p. 374. Support of the
    limit is a conclusion, including an empty compact index. *)
Theorem flat_current_mass_approximation_support (T:C):
  (forall epsilon:R,0<epsilon->exists S:C,
    flatK S /\(M (T-S)<epsilon%:E)%E)->
  support T `<=` smooth_compact_carrier K.
Proof.
move=>hApprox.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
have hChoice k:exists S:C,flatK S /\(M (T-S)<(q^+k)%:E)%E.
  exact:(hApprox (q^+k) (exprn_gt0 k (andP hq).1)).
have[u hu]:=choice hChoice.
have hWeak:=@current_mass_convergence_is_weak R h2 n m U hU u T.
apply:(@current_weak_limit_support_compact R h2 n m U hU K u T).
- apply:hWeak=>epsilon hEpsilon.
  have[k hk]:=@geometric_uniform_tail R q 1 epsilon hq (@ler01 R) hEpsilon.
  exists k=>L hKL;apply:(lt_trans (hu L).2).
  rewrite lte_fin;have h:=hk L hKL;by rewrite mulr1 in h.
- move=>k.
  exact:(@flat_current_supported_support R h2 n m U hU K (u k) (hu k).1).
Qed.

(** Source for [flat_current_mass_approximation_closed]: mass
    limits of same-index flat currents are flat in that same
    compact index. This is the closure step used with the original
    L1 density in Federer 4.1.17, p. 374. First prove support
    of the limit, then apply the original F_K<=M estimate; no
    support, finite mass or representability premise is added. *)
Theorem flat_current_mass_approximation_closed (T:C):
  (forall epsilon:R,0<epsilon->exists S:C,
    flatK S /\(M (T-S)<epsilon%:E)%E)->flatK T.
Proof.
move=>hApprox.
have hSupport:=flat_current_mass_approximation_support hApprox.
apply:flat_current_flat_approximation_closed=>epsilon hEpsilon.
have[S [hFlatS hMass]]:=hApprox epsilon hEpsilon.
have hSSupport:=@flat_current_supported_support R h2 n m U hU K S hFlatS.
have hDifference:support (T-S) `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K
    (-1) S T hSSupport hSupport.
  by rewrite scaleN1r addrC in h.
exists S;split;first exact:hFlatS.
exact:(le_lt_trans (@current_flat_norm_le_mass R h2 n m U hU K
  (T-S) hDifference) hMass).
Qed.

(** Source for [flat_current_mass_sequence_limit]: the sequential
    form of the same original closure step in Federer 4.1.17,
    p. 374. A mass-convergent sequence of flat currents with one
    common compact index has its original limit in that flat class.
    The general approximation theorem supplies the conclusion. *)
Corollary flat_current_mass_sequence_limit (u:nat->C) (T:C):
  (forall k,flatK (u k))->
  (forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    (M (T-u L)<epsilon%:E)%E)->flatK T.
Proof.
move=>hFlat hMass;apply:flat_current_mass_approximation_closed=>epsilon hEpsilon.
have[k hk]:=hMass epsilon hEpsilon.
exists (u k);split;first exact:hFlat.
exact:hk k (leqnn k).
Qed.
End FlatCurrentMassLimits.
