(** Federer (1969), 4.1.12, p. 369: the
    flat seminorm of a separated test is bounded
    by binomial(i+j+2,i+1) times the two flat
    seminorms. The exact coefficient is the Pascal
    sum of the preceding Leibniz comass bounds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentSpaces CurrentCoefficientNorms CurrentCartesianDomain CurrentCartesianTestProductSealed
  CurrentCartesianTestComass SmoothCompactSet SmoothTestSpaces SmoothFunctionTopology
  CurrentTestExteriorDerivative CurrentFlatFormSeminormLaws CurrentCompactZerothBounds
  CurrentFlatTestPointBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianFlatTestBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA k := (@current_test_space R h2 m A hA k).
Local Notation DB k := (@current_test_space R h2 n B hB k).
Local Notation va k := (@current_test_value R h2 m A hA k).
Local Notation vb k := (@current_test_value R h2 n B hB k).
Local Notation vc k := (@current_test_value R h2 (m+n) AB hAB k).
Local Notation NA k := (@current_form_comass R h2 m k).
Local Notation NB k := (@current_form_comass R h2 n k).
Local Notation NC k := (@current_form_comass R h2 (m+n) k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation Pure k l := (@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation dA k := (@current_test_exterior_derivative R h2 m k A hA).
Local Notation dB k := (@current_test_exterior_derivative R h2 n k B hB).
Local Notation dC k := (@current_test_exterior_derivative R h2 (m+n) k AB hAB).
Local Notation incC k := (smooth_test_inclusion (@current_smooth_space_laws R h2 (m+n) AB hAB k)).
Variable KA:smooth_compact_set hNX A.
Variable KB:smooth_compact_set hNY B.
Variable KAB:smooth_compact_set hNZ AB.
Hypothesis hKAB:smooth_compact_carrier KAB=
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Local Notation FA k := (@current_flat_test_seminorm R h2 m k A hA KA).
Local Notation FB k := (@current_flat_test_seminorm R h2 n k B hB KB).
Local Notation FC k := (@current_flat_test_seminorm R h2 (m+n) k AB hAB KAB).

(** Source for [current_cartesian_flat_test_bound]:
    F_(C times D)(p#alpha wedge q#beta) is at most
    binomial(i+j+2,i+1) F_C(alpha) F_D(beta),
    the separated-test estimate for the second
    inequality of Federer 4.1.12, p. 369.
    Both zero degrees and empty compacts remain allowed. *)
Theorem current_cartesian_flat_test_bound i j (alpha:DA i) (beta:DB j):
  FC (i+j) (Pure i j alpha beta)<=
    'C((i+j).+2,i.+1)%:R * (FA i alpha * FB j beta).
Proof.
pose f:=FA i alpha;pose g:=FB j beta;pose c:R:='C((i+j).+2,i.+1)%:R.
have hf:0<=f:=real_seminorm_nonnegative (@current_flat_test_is_seminorm R h2 m i A hA KA) alpha.
have hg:0<=g:=real_seminorm_nonnegative (@current_flat_test_is_seminorm R h2 n j B hB KB) beta.
have hfg:0<=f * g:=mulr_ge0 hf hg.
have hc:0<=c:=ler0n R _.
have hBin:('C(i+j,i)<='C((i+j).+2,i.+1))%N.
  have hMono:=@leq_bin2l (i+j)%N (i+j).+1 i (leqnSn (i+j)).
  rewrite binS;exact:leq_trans hMono (leq_addl _ _).
have hRealBin:'C(i+j,i)%:R<=c by rewrite /c ler_nat.
have hPascal:'C(i.+1+j,i.+1)%:R+'C(i+j.+1,i)%:R=c.
  by rewrite /c addSn addnS -natrD -binS.
have hPair a b d:0<=a->0<=b->a<=f->b<=g->0<=d->d * (a * b)<=d * (f * g).
  move=>ha hb hAf hBg hd;exact:(ler_wpM2l hd (ler_pM ha hb hAf hBg)).
have hPoints z:smooth_compact_carrier KAB z->
    NC (i+j) (vc (i+j) (Pure i j alpha beta) z)<=c * (f * g) /\
    NC (i+j).+1 (vc (i+j).+1 (dC (i+j) (Pure i j alpha beta)) z)<=c * (f * g).
  move=>hz;have hzAB:=smooth_compact_in_domain KAB z hz.
  have hRect: smooth_compact_carrier KA (p z) /\smooth_compact_carrier KB (q z).
    by move:hz;rewrite hKAB.
  have hAlpha:=@current_flat_test_point_bound R h2 m i A hA KA alpha (p z) hRect.1.
  have hDalpha:=@current_flat_test_derivative_point_bound R h2 m i A hA KA alpha (p z) hRect.1.
  have hBeta:=@current_flat_test_point_bound R h2 n j B hB KB beta (q z) hRect.2.
  have hDbeta:=@current_flat_test_derivative_point_bound R h2 n j B hB KB beta (q z) hRect.2.
  have hAP:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 m i).1 (va i alpha (p z)).
  have hBP:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 n j).1 (vb j beta (q z)).
  have hDAP:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 m i.+1).1 (va i.+1 (dA i alpha) (p z)).
  have hDBP:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 n j.+1).1 (vb j.+1 (dB j beta) (q z)).
  split.
  - apply:(le_trans (@current_cartesian_test_comass_bound R h2 m n A B hA hB i j alpha beta z hzAB)).
    apply:(le_trans (hPair _ _ _ hAP hBP hAlpha hBeta (ler0n R _))).
    exact:(ler_wpM2r hfg hRealBin).
  - apply:(le_trans (@current_cartesian_test_derivative_comass_bound R h2 m n A B hA hB i j alpha beta z hzAB)).
    have hSum:=lerD (hPair _ _ _ hDAP hBP hDalpha hBeta (ler0n R _))
      (hPair _ _ _ hAP hDBP hAlpha hDbeta (ler0n R _)).
    have hConcrete:=hSum 'C(i.+1+j,i.+1) 'C(i+j.+1,i).
    by rewrite -mulrDl hPascal in hConcrete.
rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula
  -(@current_test_exterior_derivative_inclusion R h2 (m+n) (i+j) AB hAB (Pure i j alpha beta)) ge_max.
apply/andP;split.
- apply:(@current_compact_zeroth_least_bound R h2 (m+n) (i+j) AB hAB KAB
    (incC (i+j) (Pure i j alpha beta)) (c * (f * g)) (mulr_ge0 hc hfg))=>z hz.
  exact:(hPoints z hz).1.
- apply:(@current_compact_zeroth_least_bound R h2 (m+n) (i+j).+1 AB hAB KAB
    (incC (i+j).+1 (dC (i+j) (Pure i j alpha beta))) (c * (f * g)) (mulr_ge0 hc hfg))=>z hz.
  exact:(hPoints z hz).2.
Qed.
End CurrentCartesianFlatTestBound.
