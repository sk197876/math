(** Federer (1969), 4.1.27, p. 384:
    the differential columns have an upper
    triangular expansion in consecutive simplex edges.
    Apply the already proved Chapter 1
    exterior expansion; every nonidentity permutation has
    a coefficient below the diagonal. This
    includes dependent edges and zero diagonal entries. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import GradedComponents ExteriorAlgebra ExteriorGrading FiniteExteriorPowers
  ExteriorLeibniz TriangularPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [upper_triangular_exterior_coefficients]: the triangular
    reduction of the displayed wedge differential
    in 4.1.27, p. 384, from the
    signed finite expansion of 1.3.4, p. 16.
    No inverse triangular map or independence
    of the target edge family is assumed. *)
Theorem upper_triangular_exterior_coefficients (K:fieldType) (V:lmodType K) m
    (e:'I_m->V) (a:'I_m->'I_m->K):
  (forall i j:'I_m,(j<i)%N->a i j=0)->
  e_lambda (fun i=>\sum_(j:'I_m) a i j*:e j) (ord_tuple m)=
    (\prod_(i:'I_m) a i i)*:e_lambda e (ord_tuple m).
Proof.
move=>hTriangular;apply:val_inj.
change (component_val (e_lambda (fun i=>\sum_(j:'I_m) a i j*:e j) (ord_tuple m))=
  (\prod_(i:'I_m) a i i)*:component_val (e_lambda e (ord_tuple m))).
rewrite !e_lambdaE.
change (exterior_word [seq \sum_(j<m) a i j*:e j|i<-enum 'I_m]=
  \prod_(i<m) a i i*:exterior_word [seq e i|i<-enum 'I_m]).
rewrite (@exterior_permutation_expansion K m V e a) (bigD1 1%g) //=.
have hZero:(\sum_(sigma:'S_m | sigma!=1%g)
    (\prod_(i:'I_m) a i (sigma i))*:
      exterior_word [seq e (sigma i)|i<-enum 'I_m])=0.
  apply:big1=>sigma hSigma.
  have[i hLower]:=@permutation_lower m sigma hSigma.
  have hProduct:(\prod_(j:'I_m) a j (sigma j))=0.
    by rewrite (bigD1 i) //= (hTriangular i (sigma i) hLower) mul0r.
  by rewrite hProduct scale0r.
rewrite hZero addr0.
under eq_bigr do rewrite perm1.
congr ((\prod_(i:'I_m) a i i)*:_).
apply:congr1;apply:eq_map=>i;by rewrite perm1.
Qed.
