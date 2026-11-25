(** Federer (1969), 3.4.5, p. 321: finite
    polynomial elimination supporting the real Taylor proof
    of the example cited to Cartan (1957), pp. 97–99.
    This is an internal algebra lemma. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import PolynomialCoefficientUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [distinct_degree_coefficients_independent]:
    a finite family of monic polynomials of distinct
    degrees is linearly independent, supporting the polynomial
    restriction to the cubic cone in 3.4.5, p. 321.
    The conclusion follows by finite leading-degree elimination. *)
Lemma distinct_degree_coefficients_independent (K:fieldType) (V:lmodType K)
    (I:finType) (degree:I->nat) (c:I->nat->K) (a:I->V) N:
  injective degree ->
  (forall i,c i (degree i)= 1) ->
  (forall i n,(degree i<n)%N ->c i n=0) ->
  (forall i,(degree i<N)%N \/a i=0) ->
  (forall n,\sum_i c i n*:a i=0) ->forall i,a i=0.
Proof.
move=>hInjective hMonic hAbove.
elim:N=>[|N ih] hBound hSum i.
- case:(hBound i)=>[hImpossible|//];by move:hImpossible.
- have hTop j:degree j=N ->a j=0.
    move=>hJ.
    have hEquation:=hSum N.
    rewrite (bigD1 j) //= -hJ hMonic scale1r in hEquation.
    have hOthers:(\sum_(k | k!=j) c k (degree j)*:a k)=0.
      apply:big1=>k hK.
      case:(hBound k)=>[hDegree|hZero];last by rewrite hZero scaler0.
      have hDifferent:degree k!=degree j.
        apply/eqP=>hEqual;have hSame:=hInjective k j hEqual.
        by move:hK;rewrite hSame eqxx.
      have hLess:(degree k<degree j)%N.
        rewrite hJ;have hLe:(degree k<=N)%N by rewrite -ltnS.
        rewrite hJ in hDifferent.
        by rewrite ltn_neqAle hDifferent hLe.
      by rewrite (hAbove k (degree j) hLess) scale0r.
    by rewrite hOthers addr0 in hEquation.
  have hSmaller j:(degree j<N)%N \/a j=0.
    case:(hBound j)=>[hJ|hZero];last by right.
    case:(ltngtP (degree j) N)=>[hLess|hGreater|hEqual];first by left.
    - have hBad:=leq_trans hJ hGreater;by rewrite ltnn in hBad.
    - right;exact:hTop j hEqual.
  exact:(ih hSmaller hSum i).
Qed.

(** Source for [distinct_degree_polynomials_independent]:
    vanishing of a finite sum of actual monic polynomial
    values forces its coefficients to vanish, supporting
    the cubic-cone argument in 3.4.5, p. 321.
    The internal scalar polynomial uniqueness theorem handles
    arbitrary vector coefficient spaces. *)
Theorem distinct_degree_polynomials_independent (K:fieldType) (h0:[pchar K]=i pred0)
    (V:lmodType K) (I:finType) (degree:I->nat) (c:I->nat->K) (a:I->V) N:
  injective degree ->
  (forall i,(degree i<N)%N) ->
  (forall i,c i (degree i)= 1) ->
  (forall i n,(degree i<n)%N ->c i n=0) ->
  (forall t,\sum_i (\sum_(n<N) c i n*t^+n)*:a i=0) ->
  forall i,a i=0.
Proof.
move=>hInjective hDegree hMonic hAbove hValues.
have hCoefficients n:(n<N)%N ->\sum_i c i n*:a i=0.
  apply:(@finite_power_coefficients_zero K h0 V N (fun n=>\sum_i c i n*:a i)).
  move=>t.
  have hExpand:(\sum_(n<N) t^+n*:(\sum_i c i n*:a i))=
      \sum_i (\sum_(n<N) c i n*t^+n)*:a i.
    under eq_bigr do rewrite scaler_sumr.
    rewrite exchange_big;apply:eq_bigr=>i _.
    rewrite scaler_suml;apply:eq_bigr=>k _.
    by rewrite scalerA mulrC.
  by rewrite hExpand hValues.
apply:(@distinct_degree_coefficients_independent K V I degree c a N hInjective hMonic hAbove
  (fun i=>or_introl (hDegree i)))=>n.
case:(ltnP n N)=>[hN|hN];first exact:hCoefficients n hN.
apply:big1=>i _.
have hGreater:=leq_trans (hDegree i) hN.
by rewrite (hAbove i n hGreater) scale0r.
Qed.
