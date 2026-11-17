(** Federer (1969), 3.4.7, pp. 324–325:
    actual zero-dimensional and polynomial germs test the
    original Noetherian and unique-factorization conclusions.
    Every analyticity, nonzero, and nonunit premise is proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormAnalyticUP NormAnalyticDomain NormAnalyticScalarProducts
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanScalarCoordinateAnalytic AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws
  AnalyticGermRing AnalyticGermSealed AnalyticGermValueSealed AnalyticGermValueUnits
  AnalyticGermDomain WeierstrassRegularUP WeierstrassRegularProperties WeierstrassLineRegularity
  CommutativeIdealUP CommutativeFactorizationUP CommutativePrimeLaws
  EuclideanAnalyticGermNoetherian EuclideanAnalyticGermFactorization LocalAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [local_algebra_zero_source_regression]:
    the actual nonzero constant two on R^0 is
    a unit in the Noetherian unique-factorization ring,
    retaining the scalar induction boundary of 3.4.7, p. 325. *)
Example local_algebra_zero_source_regression (R:realType):
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 0) in
  let G:=[the comNzRingType of (@analytic_germ_ring R (R_n R 0) _ hN 0)] in
  let two:G:=analytic_germ (@analytic_constant_representative R (R_n R 0) _ hN 0 2) in
  is_noetherian_commutative_ring G /\is_unique_factorization_commutative_domain G /\
    two<>0 /\is_commutative_unit two.
Proof.
move=>hN G two;split;first exact:euclidean_analytic_germ_ring_noetherian.
split;first exact:euclidean_analytic_germ_ring_factorization.
have hValue:@AnalyticGermValue.map R (R_n R 0) _ hN 0 two = 2.
  exact:(@AnalyticGermValue.laws R (R_n R 0) _ hN 0 _).
have hTwo:(2:R)!=0 by rewrite pnatr_eq0.
split.
- move=>hZero;rewrite hZero rmorph0 in hValue.
  by rewrite -hValue eqxx in hTwo.
- apply:(@analytic_germ_value_unit_equivalence R (R_n R 0) _ hN 0 two).2.
  rewrite hValue;apply/eqP;exact:hTwo.
Qed.

(** Source for [local_algebra_square_regression]: the
    actual square of the coordinate on R has
    a nonzero nonunit germ, admits a prime factorization,
    and is not prime. The repeated zero tests the
    nontrivial factorization conclusion of 3.4.7, p. 325. *)
Example local_algebra_square_regression (R:realType):
  let X:=R_n R 1 in
  let NX:=inner_norm (@euclidean_inner_productP R 1) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 1) in
  let G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)] in
  exists f:analytic_representative_type hNX (0:X),
    analytic_representative_value f=(fun x=>x ord0) /\
    let alpha:G:=analytic_germ f in
    alpha<>0 /\~is_commutative_unit alpha /\
    alpha*alpha<>0 /\~is_commutative_prime_element (alpha*alpha) /\
    exists u:G,exists F:seq G,is_commutative_unit u /\
      (forall p,p\in F ->is_commutative_prime_element p) /\
      alpha*alpha = u*\prod_(p<-F) p.
Proof.
move=>X NX hNX G.
have hAnalytic:=@euclidean_scalar_coordinate_analytic R 1 ord0.
have [f hValues]:=@analytic_representative_from_domain R X NX hNX 0 setT
  (fun x=>x ord0) (hAnalytic 0 Logic.I).
pose alpha:G:=analytic_germ f.
pose v:X:=@coordinate_basis R 1 ord0.
have hRegular:@is_weierstrass_regular_germ R X NX hNX alpha 1%N v.
  apply:(@weierstrass_line_regularity R X NX hNX f 1%N v 1 (erefl true) (oner_neq0 R))=>t.
  rewrite hValues /v /coordinate_basis !ffunE /= expr1 mul1r.
  change (t*1=t);by rewrite mulr1.
have hNonzero:alpha<>0:=@weierstrass_regular_germ_nonzero R X NX hNX alpha 1%N v hRegular.
have hNonunit:~is_commutative_unit alpha.
  move=>hUnit;have hValue:=(@analytic_germ_value_unit_equivalence R X NX hNX 0 alpha).1 hUnit.
  apply:hValue;rewrite /alpha (@AnalyticGermValue.laws R X NX hNX 0) hValues.
  by rewrite ffunE.
have hSquareNonzero:alpha*alpha<>0.
  move=>hZero;case:(@analytic_germ_no_zero_divisors R X NX hNX 0 alpha alpha hZero)=>h;exact:hNonzero h.
have hNotPrime:~is_commutative_prime_element (alpha*alpha).
  move=>hPrime.
  have hIrreducible:=@commutative_prime_irreducible G
    (@analytic_germ_no_zero_divisors R X NX hNX 0) (alpha*alpha) hPrime.
  case:(hIrreducible.2.2 alpha alpha (erefl _))=>h;exact:hNonunit h.
exists f;split;first exact:hValues.
change (alpha<>0 /\~is_commutative_unit alpha /\alpha*alpha<>0 /\
  ~is_commutative_prime_element (alpha*alpha) /\
  exists u:G,exists F:seq G,is_commutative_unit u /\
    (forall p,p\in F ->is_commutative_prime_element p) /\
    alpha*alpha = u*\prod_(p<-F) p).
split;first exact:hNonzero.
split;first exact:hNonunit.
split;first exact:hSquareNonzero.
split;first exact:hNotPrime.
exact:(@euclidean_analytic_germ_ring_factorization R 1 0).2 (alpha*alpha) hSquareNonzero.
Qed.

(** Source for [local_algebra_crossing_regression]: the
    actual product xy in R^2 is nonzero, has two
    nonunit factors, and is not prime in the original
    Noetherian unique-factorization germ ring. Independent
    coordinate lines prove both factors nonzero, testing
    3.4.7, p. 325, in positive transverse dimension. *)
Example local_algebra_crossing_regression (R:realType):
  let X:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 2) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  let G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)] in
  is_noetherian_commutative_ring G /\is_unique_factorization_commutative_domain G /\
  exists f g:analytic_representative_type hNX (0:X),
    analytic_representative_value f=(fun x=>x ord0) /\
    analytic_representative_value g=(fun x=>x ord_max) /\
    let alpha:G:=analytic_germ f in let beta:G:=analytic_germ g in
    alpha<>0 /\beta<>0 /\~is_commutative_unit alpha /\~is_commutative_unit beta /\
    alpha*beta<>0 /\~is_commutative_prime_element (alpha*beta).
Proof.
move=>X NX hNX G;split;first exact:euclidean_analytic_germ_ring_noetherian.
split;first exact:euclidean_analytic_germ_ring_factorization.
have hEach (i:'I_2):exists f:analytic_representative_type hNX (0:X),
    analytic_representative_value f=(fun x=>x i) /\
    (analytic_germ f:G)<>0 /\~is_commutative_unit (analytic_germ f:G).
  have hAnalytic:=@euclidean_scalar_coordinate_analytic R 2 i.
  have [f hValues]:=@analytic_representative_from_domain R X NX hNX 0 setT
    (fun x=>x i) (hAnalytic 0 Logic.I).
  pose v:X:=@coordinate_basis R 2 i.
  have hRegular:@is_weierstrass_regular_germ R X NX hNX (analytic_germ f) 1%N v.
    apply:(@weierstrass_line_regularity R X NX hNX f 1%N v 1 (erefl true) (oner_neq0 R))=>t.
    rewrite hValues /v /coordinate_basis !ffunE /= expr1 mul1r.
    rewrite eqxx;change (t*1=t);by rewrite mulr1.
  exists f;split;first exact:hValues.
  split;first exact:(@weierstrass_regular_germ_nonzero R X NX hNX (analytic_germ f) 1%N v hRegular).
  move=>hUnit;have hValue:=(@analytic_germ_value_unit_equivalence R X NX hNX 0 (analytic_germ f)).1 hUnit.
  apply:hValue;rewrite (@AnalyticGermValue.laws R X NX hNX 0) hValues.
  by rewrite ffunE.
have [f [hF [hFNonzero hFNonunit]]]:=hEach ord0.
have [g [hG [hGNonzero hGNonunit]]]:=hEach ord_max.
exists f,g;split;first exact:hF.
split;first exact:hG.
split;first exact:hFNonzero.
split;first exact:hGNonzero.
split;first exact:hFNonunit.
split;first exact:hGNonunit.
split.
- move=>hZero;case:(@analytic_germ_no_zero_divisors R X NX hNX 0
    (analytic_germ f) (analytic_germ g) hZero)=>h;[exact:hFNonzero h|exact:hGNonzero h].
- move=>hPrime.
  have hIrreducible:=@commutative_prime_irreducible G
    (@analytic_germ_no_zero_divisors R X NX hNX 0)
    ((analytic_germ f:G)*(analytic_germ g:G)) hPrime.
  case:(hIrreducible.2.2 (analytic_germ f) (analytic_germ g) (erefl _))=>h;
    [exact:hFNonunit h|exact:hGNonunit h].
Qed.
