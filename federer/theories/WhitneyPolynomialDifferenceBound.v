(** Federer (1969), 3.1.14, p. 226: the first estimate in the proof
    of Whitney's extension theorem. If the Taylor coefficient forms of
    two polynomials P and Q of degree at most k differ at a point b by
    at most rho d^(k-i)/(k-i)! in every order i, then at b+v they
    differ by at most rho (|v|+d)^(k-j)/(k-j)! in every order j. The
    printed display takes P=P_c, Q=P_b, x=b+v, d=|c-b| and
    rho=rho(C,|c-b|); here rho and d are abstracted as nonnegative real
    parameters. The ith differential of a polynomial is its ith Taylor
    coefficient form, as identified in 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal ring.
From Federer Require Import Hom BoundedHom RealNormUP InnerProductUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct Graded GradedSums
  GradedDegree SymmetricForms SymmetricFormSum PolynomialFunctions PolynomialRepresentations
  PolynomialTaylorTerms PolynomialTaylorCoefficients PolynomialTaylorTransform
  PolynomialTaylor PolynomialTaylorTermContinuity SymmetricOperatorNormUP
  SymmetricOperatorNorm SymmetricOperatorBoundary SymmetricOperatorTupleBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sform_finite_sum_value]: supporting evaluation
    of a finite sum of symmetric forms on one tuple, used to
    evaluate the contraction sum in the first display of Federer
    3.1.14, p. 226; the vector space structure is that of
    1.10.1, p. 44. *)
Lemma sform_finite_sum_value (K : fieldType) (V W : lmodType K) m
    (I : finType) (A : pred I) (F : I->S_m V W m) (t : m.-tuple V) :
  (\sum_(i | A i) F i) t=\sum_(i | A i) F i t.
Proof.
elim/big_ind2: _=>[|f a g b hf hg|i _] //.
by rewrite sform_addE hf hg.
Qed.

(** Source for [symmetric_taylor_term_sub]: the contraction
    v^i/i! contracted with a difference of forms is the difference
    of the contractions, supporting the first equality in the
    display of Federer 3.1.14, p. 226, by the tuple formula of
    1.10.4, p. 46. *)
Lemma symmetric_taylor_term_sub (K : fieldType) (X Y : lmodType K) m j
    (phi psi : S_m X Y m) (x : X) :
  symmetric_taylor_term j (phi-psi) x=
    symmetric_taylor_term j phi x-symmetric_taylor_term j psi x.
Proof.
case: (leqP j m)=>[hj|hj].
- apply: sform_ext=>t.
  change (symmetric_taylor_term j (phi-psi) x t=
    symmetric_taylor_term j phi x t-symmetric_taylor_term j psi x t).
  by rewrite !(symmetric_taylor_term_tuple_value hj) -scalerBr.
- by rewrite !(symmetric_taylor_term_above_degree _ x hj) subr0.
Qed.

Section OperatorNormSums.
Variable R : realType.
Variables V W : lmodType R.
Variable NV : V->R.
Hypothesis hV : is_real_seminorm NV.
Variable NW : W->R.
Hypothesis hW : is_real_seminorm NW.

(** Source for [symmetric_operator_norm_add_bound]: the operator
    norm of 1.10.5, p. 47, is subadditive, supporting the
    triangle inequality in the display of Federer 3.1.14, p. 226. *)
Lemma symmetric_operator_norm_add_bound m (f g : S_m V W m) (L M : R) :
  (symmetric_operator_norm hV NW f<=L%:E)%E ->
  (symmetric_operator_norm hV NW g<=M%:E)%E ->
  (symmetric_operator_norm hV NW (f+g)%R<=(L+M)%:E)%E.
Proof.
move=>hf hg; apply: (symmetric_operator_norm_bound hV NW _ _).2=>t ht.
rewrite sform_addE; apply: le_trans (real_seminorm_triangle hW _ _) _.
apply: lerD.
- exact: (symmetric_operator_norm_bound hV NW f L).1 hf t ht.
- exact: (symmetric_operator_norm_bound hV NW g M).1 hg t ht.
Qed.

(** Source for [symmetric_operator_norm_sum_bound]: a finite sum
    of forms with finite norm bounds has norm at most the sum of
    the bounds, the inequality in the display of Federer 3.1.14,
    p. 226. *)
Lemma symmetric_operator_norm_sum_bound m (I : finType) (A : pred I)
    (F : I->S_m V W m) (L : I->R) :
  (forall i, A i -> (symmetric_operator_norm hV NW (F i)<=(L i)%:E)%E) ->
  (symmetric_operator_norm hV NW (\sum_(i | A i) F i)%R<=(\sum_(i | A i) L i)%:E)%E.
Proof.
move=>hF; elim/big_ind2: _=>[|f a g b hf hg|i hi].
- rewrite (symmetric_operator_zero hV hW); exact: lexx.
- exact: symmetric_operator_norm_add_bound hf hg.
- exact: hF.
Qed.
End OperatorNormSums.

(** Source for [symmetric_taylor_term_operator_bound]: the estimate
    ||v^i/i! contracted with phi|| <= (|v|^i/i!) ||phi|| used in the
    display of Federer 3.1.14, p. 226, from the unit-tuple definition
    of the operator norm in 1.10.5, p. 47, and the tuple formula for
    the contraction in 1.10.4, p. 46. *)
Lemma symmetric_taylor_term_operator_bound (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    m j (hj : (j<=m)%N) (phi : S_m X Y m) (x : X) (L : R) :
  (symmetric_operator_norm hNX.1 NY phi<=L%:E)%E ->
  (symmetric_operator_norm hNX.1 NY (symmetric_taylor_term j phi x)
    <=(L*(NX x^+(m-j)/((m-j)`!)%:R))%:E)%E.
Proof.
move=>hL.
have hL0 : 0<=L.
  have hh := le_trans (symmetric_operator_norm_ge_zero hNX.1 hNY.1 phi) hL.
  by move: hh; rewrite lee_fin.
have hx0 : 0<=NX x^+(m-j) := exprn_ge0 _ (real_seminorm_nonnegative hNX.1 x).
have hc0 : 0<=(((m-j)`!)%:R : R)^-1 by rewrite invr_ge0 ler0n.
apply: (symmetric_operator_norm_bound hNX.1 NY _ _).2=>t ht.
rewrite (symmetric_taylor_term_tuple_value hj) (real_seminorm_scale hNY.1).
set u := tcast _ _.
have hu : \prod_(i<m) NX (tnth u i)=(\prod_(i<j) NX (tnth t i))*NX x^+(m-j).
  rewrite -(@big_tuple R 1 *%R X m u predT NX) /u val_tcast /= big_cat
    (@big_tuple R 1 *%R X j t predT NX)
    (@big_tuple R 1 *%R X (m-j) [tuple x | _<m-j] predT NX).
  congr (_*_).
  under eq_bigr do rewrite tnth_mktuple.
  by rewrite prodr_const card_ord.
have hprod : \prod_(i<j) NX (tnth t i)<=1.
  apply: prodr_ile1=>i _; apply/andP; split.
  - exact: real_seminorm_nonnegative hNX.1 _.
  - exact: ht i.
have hb := symmetric_operator_finite_tuple_bound hNY.1 hL u.
rewrite hu in hb.
rewrite (ger0_norm hc0).
apply: le_trans (ler_wpM2l hc0 hb) _.
have hh : L*((\prod_(i<j) NX (tnth t i))*NX x^+(m-j))<=L*NX x^+(m-j).
  apply: (ler_wpM2l hL0); exact: (ler_piMl hx0 hprod).
apply: le_trans (ler_wpM2l hc0 hh) _.
have -> : L*(NX x^+(m-j)/((m-j)`!)%:R)=((m-j)`!)%:R^-1*(L*NX x^+(m-j)) by ring.
exact: lexx.
Qed.

(** Source for [whitney_divided_binomial_sum]: the last equality in
    the display of Federer 3.1.14, p. 226, the binomial identity
    sum_(i<=k-j) (x^i/i!) (y^(k-j-i)/(k-j-i)!) = (x+y)^(k-j)/(k-j)!,
    indexed by the order m=i+j of the contracted coefficient. *)
Lemma whitney_divided_binomial_sum (R : numFieldType) (x y : R) k j :
  (j<=k)%N ->
  \sum_(m<k.+1 | (j<=m)%N) y^+(k-m)/((k-m)`!)%:R*(x^+(m-j)/((m-j)`!)%:R)
    =(x+y)^+(k-j)/((k-j)`!)%:R.
Proof.
move=>hjk.
have -> : \sum_(m<k.+1 | (j<=m)%N) y^+(k-m)/((k-m)`!)%:R*(x^+(m-j)/((m-j)`!)%:R)
    =\sum_(j<=m<k.+1) y^+(k-m)/((k-m)`!)%:R*(x^+(m-j)/((m-j)`!)%:R).
  by rewrite big_geq_mkord.
have -> : \sum_(j<=m<k.+1) y^+(k-m)/((k-m)`!)%:R*(x^+(m-j)/((m-j)`!)%:R)
    =\sum_(i<(k-j).+1) y^+(k-(i+j))/((k-(i+j))`!)%:R*(x^+(i+j-j)/((i+j-j)`!)%:R).
  by have := big_addn 0 k.+1 j xpredT
    (fun m=>y^+(k-m)/((k-m)`!)%:R*(x^+(m-j)/((m-j)`!)%:R));
    rewrite add0n (subSn hjk)=>->; rewrite big_mkord.
rewrite [x+y]addrC exprDn mulr_suml.
apply: eq_bigr=>i _.
have hi : (i<=k-j)%N := ltn_ord i.
rewrite addnK addnC subnDA.
have hC : (('C(k-j,i))%:R : R)!=0 by rewrite pnatr_eq0 -lt0n bin_gt0.
rewrite -(bin_fact hi) !natrM -[_ *+ 'C(k-j,i)]mulr_natl invfM [in RHS]mulrACA
  (mulfV hC) mul1r.
by rewrite invfM; ring.
Qed.

Section Whitney.
Variable R : realType.
Variable m : nat.
Local Notation X := (R_n R m).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable k : nat.

(** Source for [whitney_polynomial_difference_bound]: Federer 3.1.14,
    p. 226, the first display of the proof: if c,b in C subset A,
    x in R^m and j<=k, then
    ||D^j P_c(x)-D^j P_b(x)||
      =||sum_(i<=k-j) (x-b)^i/i! contracted with [D^(j+i) P_c(b)-D^(j+i) P_b(b)]||
      <=sum_(i<=k-j) (|x-b|^i/i!) [|c-b|^(k-j-i)/(k-j-i)!] rho(C,|c-b|)
      =[(|x-b|+|c-b|)^(k-j)/(k-j)!] rho(C,|c-b|).
    This supporting estimate abstracts P_c and P_b as polynomials P
    and Q of degree at most k, x-b as v, |c-b| as d and rho(C,|c-b|)
    as rho. The order-i hypothesis for i<=k is the definition of
    rho(C,delta) on p. 225 applied to the pair c,b. *)
Theorem whitney_polynomial_difference_bound
    (P Q : PolynomialFunction X Y) (b v : X) (d rho : R) :
  (polynomial_degree P<=k)%N -> (polynomial_degree Q<=k)%N -> 0<=d -> 0<=rho ->
  (forall i, (i<=k)%N ->
    (symmetric_operator_norm hN.1 NY
      (polynomial_taylor_coefficient P i b-polynomial_taylor_coefficient Q i b)%R
      <=(rho*d^+(k-i)%N/((k-i)%N)`!%:R)%:E)%E) ->
  forall j, (j<=k)%N ->
    (symmetric_operator_norm hN.1 NY
      (polynomial_taylor_coefficient P j (b+v)-polynomial_taylor_coefficient Q j (b+v))%R
      <=(rho*(N v+d)^+(k-j)%N/((k-j)%N)`!%:R)%:E)%E.
Proof.
move=>hP hQ hd hrho hcoef j hjk.
have hjk1 : (j<k.+1)%N by [].
have hfP : grade_bounded (S_star_grading X Y) (polynomial_to_forms P) k.+1.
  exact: (grade_bounded_mono (hP : ((polynomial_degree P).+1<=k.+1)%N)
    (@graded_degree_bound R _ (S_star_grading X Y) (polynomial_to_forms P))).
have hfQ : grade_bounded (S_star_grading X Y) (polynomial_to_forms Q) k.+1.
  exact: (grade_bounded_mono (hQ : ((polynomial_degree Q).+1<=k.+1)%N)
    (@graded_degree_bound R _ (S_star_grading X Y) (polynomial_to_forms Q))).
rewrite /polynomial_taylor_coefficient
  (symmetric_taylor_coefficient_translation (@pchar_num R) b v hfP hjk1)
  (symmetric_taylor_coefficient_translation (@pchar_num R) b v hfQ hjk1)
  /taylor_coefficient -sumrB.
under eq_bigr do rewrite -symmetric_taylor_term_sub.
pose L (i : nat) : R := rho*d^+(k-i)/((k-i)`!)%:R*(N v^+(i-j)/((i-j)`!)%:R).
have hsum : (symmetric_operator_norm hN.1 NY
    (\sum_(i<k.+1 | (j<=i)%N) symmetric_taylor_term j
      (polynomial_taylor_coefficient P i b-polynomial_taylor_coefficient Q i b) v)%R
    <=(\sum_(i<k.+1 | (j<=i)%N) L i)%:E)%E.
  apply: (@symmetric_operator_norm_sum_bound R X Y N hN.1 NY hNY.1 j _ _ _ _)=>i hi.
  have hik : (i<=k)%N by move: (ltn_ord i); rewrite ltnS.
  exact: (@symmetric_taylor_term_operator_bound R X Y N NY hN hNY i j hi _ v _
    (hcoef i hik)).
apply: le_trans hsum _.
rewrite lee_fin.
have -> : \sum_(i<k.+1 | (j<=i)%N) L i
    =rho*\sum_(i<k.+1 | (j<=i)%N) d^+(k-i)/((k-i)`!)%:R*(N v^+(i-j)/((i-j)`!)%:R).
  rewrite mulr_sumr; apply: eq_bigr=>i _; by rewrite /L !mulrA.
rewrite (whitney_divided_binomial_sum (N v) d hjk) mulrA.
exact: lexx.
Qed.
End Whitney.
