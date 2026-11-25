(** Federer (1969), 4.1.12, p. 367: the
    original dual flat supremum is nonnegative and
    gives the exact finite homogeneous evaluation bound.
    All statements start with an algebraic functional;
    continuity is a later conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet ExtendedSupremumUP
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormUP CurrentFlatDualSeminormSealed
  SeminormFunctionalUnitBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatDualSeminormBasic.
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
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation F := (@current_flat_test_seminorm R h2 n m U hU K).

Local Notation hF := (@current_flat_test_is_seminorm R h2 n m U hU K).
Local Notation Dual := (@CurrentFlatDualSeminorm.value R h2 n m U hU K).
Local Notation hDual := (@CurrentFlatDualSeminorm.laws R h2 n m U hU K).

(** Source for [current_flat_dual_nonnegative]: zero is
    an admissible original test, hence F_K(T)>=0,
    supporting Federer 4.1.12, p. 367, for every
    algebraic real linear functional. *)
Lemma current_flat_dual_nonnegative (T:Hom DT R^o):(0<=Dual T)%E.
Proof.
apply:(extended_supremum_nonnegative (hDual T)).
exists 0;split;last exact:lexx.
exists (0:DT);split.
- by rewrite (real_seminorm_zero hF) ler01.
- exact:linear0.
Qed.

(** Source for [current_flat_dual_unit_upper]: the
    original supremum bounds every admissible test,
    supporting Federer 4.1.12, p. 367. *)
Lemma current_flat_dual_unit_upper (T:Hom DT R^o) phi:
  F phi<=1->((T phi)%:E<=Dual T)%E.
Proof.
move=>hPhi;apply:(extended_supremum_upper (hDual T)).
by exists phi.
Qed.

(** Source for [current_flat_dual_unit_absolute]: the
    symmetric flat unit ball bounds the absolute action,
    supporting Federer 4.1.12, p. 367. *)
Lemma current_flat_dual_unit_absolute (T:Hom DT R^o) phi:
  F phi<=1->(`|T phi|%:E<=Dual T)%E.
Proof.
move=>hPhi;case:(leP 0 (T phi))=>hSign.
- rewrite (ger0_norm hSign);exact:current_flat_dual_unit_upper.
- rewrite (ltr0_norm hSign).
  have hNegative:F (-phi)<=1 by rewrite (real_seminorm_negate hF).
  have h:=current_flat_dual_unit_upper T hNegative.
  by rewrite linearN in h.
Qed.

(** Source for [current_flat_dual_finite_value]: a finite
    original F_K(T) is a nonnegative real value,
    supporting Federer 4.1.12, p. 367. *)
Lemma current_flat_dual_finite_value (T:Hom DT R^o):
  (Dual T < +oo)%E->exists c:R,0<=c /\ Dual T=c%:E.
Proof.
move=>hFinite.
have hNonnegative:=current_flat_dual_nonnegative T.
have hNumber:Dual T \is a fin_num.
  rewrite (ge0_fin_numE hNonnegative);exact:hFinite.
exists (fine (Dual T));split.
- have hValue:Dual T=(fine (Dual T))%:E by rewrite fineK.
  by rewrite hValue lee_fin in hNonnegative.
- by rewrite fineK.
Qed.

(** Source for [current_flat_dual_finite_bound]: the exact
    bound |T(phi)|<=F_K(T) F_K(phi), with the finite
    dual value expressed as a real c, supports
    Federer 4.1.12, p. 367. Zero-seminorm tests
    are handled before normalization. *)
Theorem current_flat_dual_finite_bound (T:Hom DT R^o) c:
  Dual T=c%:E->forall phi,`|T phi|<=c * F phi.
Proof.
move=>hValue phi;apply:(@seminorm_functional_unit_bound R DT F hF T c)=>psi hPsi.
have h:=current_flat_dual_unit_absolute T hPsi.
by rewrite hValue lee_fin in h.
Qed.

(** Source for [current_flat_dual_upper_from_bound]: an
    original homogeneous flat bound controls the dual
    supremum, supporting Federer 4.1.12, p. 367. *)
Theorem current_flat_dual_upper_from_bound (T:Hom DT R^o) c:
  0<=c->(forall phi,`|T phi|<=c * F phi)->(Dual T<=c%:E)%E.
Proof.
move=>hc hBound;apply:(extended_supremum_least (hDual T))=>a [phi [hPhi <-]].
rewrite lee_fin.
apply:(le_trans (ler_norm (T phi)));apply:(le_trans (hBound phi)).
have h:=ler_wpM2l hc hPhi.
by rewrite mulr1 in h.
Qed.
End CurrentFlatDualSeminormBasic.
