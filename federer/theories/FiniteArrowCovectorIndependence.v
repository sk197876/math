(** Federer (1969), 3.4.8(10), pp. 331–332:
    the original equation differentials are independent.
    Connect their special transverse matrix to
    the biorthogonal independence theorem already
    proved for 1.4.3, p. 19. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom Bilinear FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_arrow_covectors_independent]:
    the first differential has a nonzero
    first transverse entry; all remaining
    transverse columns have the same nonzero
    diagonal and vanish off that diagonal,
    3.4.8(10), pp. 331–332. Construct
    biorthogonal test vectors and apply 1.4.3;
    no determinant or rank conclusion is assumed. *)
Theorem finite_arrow_covectors_independent (K:fieldType) (X:lmodType K)
    (index:finType) (first:index) (D:index->Hom X K^o) (v:index->X) (delta:K):
  delta!=0 ->D first (v first)!=0 ->
  (forall i j,j!=first ->D i (v j) = delta*(if i==j then 1 else 0)) ->
  finite_independent D.
Proof.
move=>hDelta hFirst hMatrix.
pose normalized j:=delta^-1 *:v j.
have hNormalized i j (hJ:j!=first):D i (normalized j) = if i==j then 1 else 0.
  rewrite /normalized (linZ (hom_linear (D i))) (hMatrix i j hJ).
  change (delta^-1*(delta*(if i==j then 1 else 0)) = if i==j then 1 else 0).
  by rewrite mulrA mulVf // mul1r.
pose correction:=\sum_(j | j!=first) D j (v first)*:normalized j.
have hCorrection i:D i correction = if i==first then 0 else D i (v first).
  have hSum:D i correction = \sum_(j | j!=first) D j (v first)*(if i==j then 1 else 0).
    rewrite /correction (linear_sum (hom_as_linear (D i)));apply:eq_bigr=>j hj.
    change (D i (D j (v first)*:normalized j) = D j (v first)*(if i==j then 1 else 0)).
    by rewrite (linZ (hom_linear (D i))) (hNormalized i j hj).
  rewrite hSum;case:(eqVneq i first)=>[->|hOther].
  - apply:big1=>j hj;by rewrite eq_sym (negbTE hj) mulr0.
  - rewrite (bigD1 i) //= eqxx mulr1.
    have hZero:(\sum_(j | (j!=first) && (j!=i)) D j (v first)*(if i==j then 1 else 0)) = 0.
      apply:big1=>j /andP [_ hj];by rewrite eq_sym (negbTE hj) mulr0.
    by rewrite hZero addr0.
pose u j:=if j==first then (D first (v first))^-1 *:(v first-correction) else normalized j.
have hPair i j:D i (u j) = if i==j then 1 else 0.
  rewrite /u;case:(eqVneq j first)=>[->|hJ].
  - rewrite (linZ (hom_linear (D i))) (linB (hom_linear (D i))) hCorrection.
    case:(eqVneq i first)=>[->|hI].
    + change ((D first (v first))^-1*(D first (v first)-0) = 1).
      by rewrite subr0 mulVf.
    + change ((D first (v first))^-1*(D i (v first)-D i (v first)) = 0).
      by rewrite subrr mulr0.
  - exact:hNormalized i j hJ.
pose test i:=@HomMap K (Hom X K^o) K^o (fun L:Hom X K^o=>L (u i))
  (introT (asboolP _) (@hom_eval_linear K X K^o (u i))).
apply:(@finite_independent_separating K index (Hom X K^o) D
  (fun i=>hom_as_linear (test i)))=>i j.
change (D j (u i) = if i==j then 1 else 0).
by rewrite hPair eq_sym.
Qed.
