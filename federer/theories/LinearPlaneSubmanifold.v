(** Federer (1969), 3.1.19, p. 231: linear planes are elementary
    examples of submanifolds, supplying regressions for every
    dimension and finite class, including degree and class zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormDiffeomorphismUP NormDiffeomorphismComposition NormOpenDomainLaws EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [linear_plane_submanifold]: supporting example
    of the straightening definition of Federer 3.1.19, p. 231.
    Identity coordinates straighten any mu-plane in R^n, at every
    class, without imposing nonemptiness of its complement. *)
Lemma linear_plane_submanifold (R:realType) n mu k (Z:G (R_n R n) mu) :
  @is_euclidean_submanifold R n mu k (grassmann_val Z).
Proof.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose I:=hom_of_linear (linear_id X).
have hI:norm_bounded_linear NX NX I.
  exists 1; split; first exact: ler01.
  by move=>x; change (NX x<=1*NX x); rewrite mul1r.
have hd:=@norm_linear_diffeomorphism R X X NX NX hNX hNX I I k hI hI
  (fun x=>erefl x) (fun x=>erefl x).
move=>b hb; exists setT,setT,I,I,Z; constructor.
- exact: norm_full_domain_interior.
- exact hd.
- apply/seteqP; split=>x.
  + move=>[y [hy _] <-]; by split.
  + move=>[hx _]; exists x.
    * by split.
    * by [].
Qed.
