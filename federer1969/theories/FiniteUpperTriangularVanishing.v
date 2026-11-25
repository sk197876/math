(** Federer (1969), 3.4.5, p. 321: finite
    coefficient elimination supporting the local/global analytic
    example cited to Cartan (1957), pp. 97–99.
    This internal algebra lemma is not a separate book claim. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_upper_triangular_vanishing]: finite
    triangular coefficient identities force all original
    coefficients to vanish, supporting the actual Taylor
    argument for the example cited in 3.4.5, p. 321. *)
Lemma finite_upper_triangular_vanishing (K:fieldType) (V:lmodType K)
    (c:nat->nat->K) (a:nat->V) N:
  (forall i,c i i= 1) ->
  (forall i,(i<N)%N ->\sum_(k<N | (i<=k)%N) c i k *: a k=0) ->
  forall k,(k<N)%N ->a k=0.
Proof.
move=>hDiagonal;elim:N=>[|N ih] hSum k hk;first by [].
have hLast:a N=0.
  have hEquation:=hSum N (ltnSn N).
  rewrite big_mkcond big_ord_recr /= leqnn hDiagonal scale1r in hEquation.
  have hPrefix:(\sum_(j<N) if (N<=j)%N then c N j *: a j else 0)=0.
    apply:big1=>j _.
    have hNo:~~(N<=j)%N by rewrite -ltnNge;exact:ltn_ord j.
    by rewrite (negbTE hNo).
  by rewrite hPrefix add0r in hEquation.
case:(ltngtP k N)=>[hLess|hGreater|hEqual].
- apply:ih hLess=>i hi.
  have hEquation:=hSum i (ltn_trans hi (ltnSn N)).
  rewrite big_mkcond big_ord_recr /= hLast scaler0 if_same addr0 in hEquation.
  by rewrite -big_mkcond in hEquation.
- have hImpossible:=leq_trans hk hGreater.
  by rewrite ltnn in hImpossible.
- by rewrite hEqual.
Qed.

(** Source for [finite_signed_binomial_vanishing]: the
    actual finite binomial transform arising from substituting
    y^2=-x^2+t*x^3 is injective, supporting the analytic
    counterexample cited in 3.4.5, p. 321. *)
Lemma finite_signed_binomial_vanishing (K:fieldType) (V:lmodType K)
    (a:nat->V) N:
  (forall i,(i<N)%N ->\sum_(k<N | (i<=k)%N)
    (('C(k,i))%:R*(-1)^+(k-i))*:a k=0) ->
  forall k,(k<N)%N ->a k=0.
Proof.
have hDiagonal i:(('C(i,i))%:R*(-1)^+(i-i):K)= 1 by rewrite binn subnn expr0 mulr1.
exact:(@finite_upper_triangular_vanishing K V (fun i k=>('C(k,i))%:R*(-1)^+(k-i)) a N hDiagonal).
Qed.
