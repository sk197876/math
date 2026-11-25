(** Federer (1969), 4.1.12, p. 368: independently
    specify the mass closure of the original supported
    normal currents. Such a closure retains the compact
    support constraint and lies in the original flat
    closure, by testwise support and F_K<=M. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentSupportGeometry
  CurrentMassSealed CurrentFlatNorm CurrentFlatMassComparison NormalCurrentsUP FlatCurrentsUP
  CurrentWeakLimitOperations CurrentMassWeakConvergence GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalMassClosure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation normalK := (@normal_currents_supported_in R h2 n U hU m K).

(** Source for [is_normal_current_mass_closure]: the
    literal M closure of N_(m,K), as used
    in Federer 4.1.12, p. 368. Every
    tolerance admits a normal approximant supported in K.
    Support of the limit is a later conclusion. *)
Definition is_normal_current_mass_closure (T:C):Prop:=
  forall epsilon:R,0<epsilon->exists S:C,normalK S /\(M (T-S)<epsilon%:E)%E.

(** Source for [normal_current_mass_closure_support]: the
    M closure of N_(m,K) retains support in K,
    supporting Federer 4.1.12, p. 368. Choose
    geometric mass approximants and reuse original weak
    support preservation; no support premise is imposed on T. *)
Theorem normal_current_mass_closure_support (T:C):
  is_normal_current_mass_closure T->support T `<=` smooth_compact_carrier K.
Proof.
move=>hClosure.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
have hChoice k:exists S:C,normalK S /\(M (T-S)<(q^+k)%:E)%E.
  exact:(hClosure (q^+k) (exprn_gt0 k (andP hq).1)).
have[u hu]:=choice hChoice.
have hWeak:=@current_mass_convergence_is_weak R h2 n m U hU u T.
apply:(@current_weak_limit_support_compact R h2 n m U hU K u T).
- apply:hWeak=>epsilon hEpsilon.
  have[k hk]:=@geometric_uniform_tail R q 1 epsilon hq (@ler01 R) hEpsilon.
  exists k=>L hKL;apply:(lt_trans (hu L).2).
  rewrite lte_fin;have h:=hk L hKL;by rewrite mulr1 in h.
- move=>k;exact:(hu k).1.2.
Qed.

(** Source for [normal_current_mass_closure_is_flat]: the
    original M closure of N_(m,K) lies in F_(m,K),
    supporting Federer 4.1.12, p. 368, by
    the preceding F_K<=M bound. No absence-of-fillings
    hypothesis is needed for this direction. *)
Theorem normal_current_mass_closure_is_flat (T:C):
  is_normal_current_mass_closure T->@is_flat_current_supported_in R h2 n m U hU K T.
Proof.
move=>hClosure.
have hSupport:=normal_current_mass_closure_support hClosure.
move=>epsilon hEpsilon.
have[S [hNormal hApprox]]:=hClosure epsilon hEpsilon.
exists S;split;first exact:hNormal.
have hDifference:support (T-S) `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K (-1) S T hNormal.2 hSupport.
  by rewrite scaleN1r addrC in h.
exact:(le_lt_trans (@current_flat_norm_le_mass R h2 n m U hU K (T-S) hDifference) hApprox).
Qed.
End CurrentNormalMassClosure.
