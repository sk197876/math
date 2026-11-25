(** Federer (1969), 4.1.12, p. 368: on a
    compact set supporting no nonzero normal filling,
    original flat chains have mass equal to their
    flat norm. Approximate by normal chains, use
    the finite-mass minimum, and pass to the limit
    with the preceding weak mass lower-limit theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentSupportGeometry
  CurrentFlatNorm CurrentFlatMassComparison CurrentFlatNormalNullFilling CurrentMassSealed CurrentMassBasic
  CurrentMassWeakLowerLimit NormalCurrentsUP CompactRepresentedCurrentMass FlatCurrentsUP FlatCurrentFinite
  FlatCurrentSpaces LinearSubspaceRepresentationUP FlatCurrentNormalWeakApproximation GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentMassNoFillings.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation V := (@flat_current_space R h2 n m U hU K).
Local Notation inc := (@flat_current_inclusion R h2 n m U hU K).
Local Notation hV := (@flat_current_space_laws R h2 n m U hU K).
Local Notation N := (@flat_current_norm R h2 n m U hU K).
Local Notation hN := (@flat_current_norm_is_norm R h2 n m U hU K).
Hypothesis hNoFilling:forall S:@current_space R h2 n U hU m.+1,
  @is_normal_current R h2 n U hU m.+1 S->
  @current_support R h2 n U hU m.+1 S `<=` smooth_compact_carrier K->S=0.

(** Source for [flat_current_mass_equals_flat_no_fillings]:
    F_K(T)=M(T)<infinity for every original flat T
    supported with index K, when K supports no
    nonzero normal filling. This justifies the passage
    from the normal-minimiser parenthesis to the mass
    closure in Federer 4.1.12, p. 368;
    no finite-mass premise is imposed on T. *)
Theorem flat_current_mass_equals_flat_no_fillings (T:C):
  @is_flat_current_supported_in R h2 n m U hU K T->F T=M T /\(M T< +oo)%E.
Proof.
move=>hFlat.
have[u [hNormal [hError hWeak]]]:=@flat_current_normal_weak_approximation R h2 n m U hU K T hFlat.
have[v hv]:=subspace_representation_full hV hFlat.
have hRepresent k:exists w:V,inc w=u k.
  exact:(subspace_representation_full hV
    (@supported_normal_current_is_flat R h2 n m U hU K (u k) (hNormal k))).
have[w hw]:=choice hRepresent.
have hValue:F T=(N v)%:E.
  rewrite -hv;exact:flat_current_norm_value.
have hProduct k:F (u k)=(N (w k))%:E.
  rewrite -(hw k);exact:flat_current_norm_value.
have hMass k:M (u k)=(N (w k))%:E.
  rewrite -hProduct; symmetry.
  exact:(@current_flat_equals_mass_no_normal_fillings R h2 n m U hU K hNoFilling
    (u k) (hNormal k).2 (@compact_represented_current_finite_mass R h2 n m U hU (u k)
      (hNormal k).1.1.1 (hNormal k).1.2)).
have hBound delta (hDelta:0<delta):(M T<=(N v+delta)%:E)%E.
  have hq:0<(1/2:R)<1 by apply/andP;split;lra.
  have[k hk]:=@geometric_uniform_tail R (1/2) 1 delta hq (@ler01 R) hDelta.
  apply:(@current_mass_weak_closed_bound R h2 n m U hU u T (N v+delta)%:E k hWeak)=>L hKL.
  have hDifference:F (T-u L)=(N (v-w L))%:E.
    have h:=@flat_current_norm_value R h2 n m U hU K (v-w L).
    by rewrite (linB (hom_linear inc)) hv (hw L) in h.
  have hSmall:N (v-w L)<delta.
    have h:=hError L;rewrite hDifference lte_fin in h.
    have hTail:=hk L hKL;rewrite mulr1 in hTail.
    exact:lt_trans h hTail.
  have hTriangle:=real_seminorm_triangle hN.1 v (w L-v).
  rewrite addrC subrK (real_seminorm_subtract hN.1) in hTriangle.
  rewrite (hMass L) lee_fin.
  exact:le_trans hTriangle (lerD (lexx _) (ltW hSmall)).
have hFinite:(M T< +oo)%E:=le_lt_trans (hBound 1 ltr01) (ltry _).
have[b [hb hB]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hUpper:b<=N v.
  apply/ler_addgt0Pr=>delta hDelta.
  have h:=hBound delta hDelta;by rewrite hB lee_fin in h.
split;last exact:hFinite.
apply/eqP;rewrite eq_le;apply/andP;split.
- exact:(@current_flat_norm_le_mass R h2 n m U hU K T
    (@flat_current_supported_support R h2 n m U hU K T hFlat)).
- by rewrite hValue hB lee_fin.
Qed.
End FlatCurrentMassNoFillings.
