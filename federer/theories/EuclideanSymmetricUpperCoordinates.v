(** Federer (1969), 3.2.28(1), printed p. 263: the
    independent upper-triangular entries of a symmetric
    endomorphism. Their coordinate generators are local basis
    witnesses for the dimension count, not a new definition of Y_m. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations
  EuclideanSymmetricCoordinates EuclideanSymmetricGenerators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_symmetric_indices]: independent
    pairs i<=j in the dimension count of Federer
    3.2.28(1), p. 263. The index predicate retains
    exactly one of the two transposed off-diagonal entries. *)
Definition euclidean_symmetric_indices m:finType:=
  Finite.clone {p:('I_m*'I_m)%type | (p.1<=p.2)%N} _.

(** Source for [euclidean_symmetric_upper_coefficient]: an
    upper-triangular coordinate extracts precisely its own
    symmetric generator coefficient, supporting the basis
    assertion in Federer 3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_upper_coefficient (R:realType) m
    (a b:euclidean_symmetric_indices m):
  euclidean_hom_coefficient
    (@euclidean_symmetric_generator R m (val a).1 (val a).2)
    (val b).1 (val b).2=if a==b then 1 else 0.
Proof.
case:a=>[[i j] hij]; case:b=>[[r s] hrs].
rewrite euclidean_symmetric_generator_coefficient.
have hCross:(if i==j then (0:R) else
    (if s==i then 1 else 0)*(if r==j then 1 else 0))=0.
  case:ifP=>hijEq; first reflexivity.
  case:(eqVneq s i)=>[hsi|hsi]; last by rewrite mul0r.
  rewrite mul1r.
  case:(eqVneq r j)=>[hrj|hrj]; last reflexivity.
  exfalso.
  have hji:(j<=i)%N by move:hrs; rewrite hrj hsi.
  have heq:i=j.
    apply:val_inj; apply/eqP; by rewrite eqn_leq hij hji.
  by move:hijEq; rewrite heq eqxx.
rewrite hCross addr0.
change ((if s==j then (1:R) else 0)*(if r==i then 1 else 0)=
  if (i==r)&&(j==s) then 1 else 0).
rewrite [s==j]eq_sym [r==i]eq_sym.
by case:(i==r); case:(j==s); rewrite ?mul1r ?mul0r.
Qed.
