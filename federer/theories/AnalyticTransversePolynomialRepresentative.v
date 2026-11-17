(** Federer (1969), 3.4.7, p. 325: every
    finite transverse polynomial has its actual analytic
    representative and original ring-sum germ. Coefficient
    representatives and the finite sum stay local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  AnalyticGermFiniteSum AnalyticTransverseMonomial WeierstrassTransverseUP WeierstrassTransversePullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Representative.
Variable R:realType.
Variables X K:lmodType R.
Variable NX:X->R.
Variable NK:K->R.
Hypothesis hNX:is_real_norm NX.
Hypothesis hNK:is_real_norm NK.
Variable v:X.
Variable xi:Hom X R^o.
Variable inclusion:Hom K X.
Variable projection:Hom X K.
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation E:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).

(** Source for [analytic_transverse_polynomial_representative]: the
    original finite polynomial expression and the ring
    polynomial have the same actual analytic germ,
    supporting the identification of P in 3.4.7, p. 325. *)
Theorem analytic_transverse_polynomial_representative k
    (c:nat->@analytic_representative_type R K NK hNK (projection 0)):
  (forall x,analytic_representative_value fXi x = xi x) ->
  exists f:@analytic_representative_type R X NX hNX 0,
    (forall x,analytic_representative_value f x =
      \sum_(i<k) (xi x)^+i*analytic_representative_value (c i) (projection x)) /\
    (analytic_germ f:G) = \sum_(i<k) E (analytic_germ (c i))*Gamma^+i.
Proof.
move=>hXi.
have hTerms i:=@analytic_transverse_monomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi (c i) i hXi.
pose term i:=projT1 (cid (hTerms i)).
have hTermValues i x:analytic_representative_value (term i) x =
    (xi x)^+i*analytic_representative_value (c i) (projection x):=
  (projT2 (cid (hTerms i))).1 x.
have hTermGerm i:(analytic_germ (term i):G) = E (analytic_germ (c i))*Gamma^+i:=
  (projT2 (cid (hTerms i))).2.
pose terms:=map (fun i:'I_k=>term (i:nat)) (enum 'I_k).
have [f [hValues hGerm]]:=@analytic_finite_sum_representative R X NX hNX 0 terms.
exists f;split.
- move=>x;rewrite hValues /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _;exact:hTermValues.
- rewrite hGerm /terms big_map -[RHS]big_enum.
  apply:eq_bigr=>i _;exact:hTermGerm.
Qed.
End Representative.
