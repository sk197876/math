(** Federer (1969), 3.2.31, p. 269: a positive exterior
    degree exceeding the differential rank forces a complementary
    direction in each basis word. This supplies a small coefficient
    in every exterior image of the approximating automorphism. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP OrthonormalFamilies
  LinearRankAtLeast ExteriorIndices LambdaPermutation FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [low_rank_projection_word_zero_eigenvalue]:
    supporting norm(Lambda^mu t)<epsilon in Federer 3.2.31,
    p. 269. If all selected directions of a mu-word were
    fixed by the range projection, their independent vectors
    would lift to independent images of the original map,
    contradicting its rank bound. No dimension bound on mu
    is imposed; above-ambient word families are empty. *)
Theorem low_rank_projection_word_zero_eigenvalue (R:realType) m v mu
    (D:Hom (R_n R m) (R_n R v)) (P:Hom (R_n R v) (R_n R v))
    (e:'I_v->R_n R v) (c:'I_v->R):
  orthonormal_family (@euclidean_inner_product R v) e ->
  (forall i,P (e i)=c i*:e i) ->
  (forall i,c i=0 \/c i= 1) ->
  (forall y,P y=y ->exists x,D x=y) ->
  ~linear_rank_at_least D mu ->
  forall lambda:Lambda v mu,exists i:'I_mu,c (tnth (val lambda) i)=0.
Proof.
move=>hOrtho hEigen hBinary hRange hRank lambda.
case:(pselect (exists i:'I_mu,c (tnth (val lambda) i)=0))=>hEx; first exact hEx.
exfalso; apply:hRank.
have hOne i:c (tnth (val lambda) i)= 1.
  case:(hBinary (tnth (val lambda) i))=>hh; last exact hh.
  exfalso; apply:hEx; by exists i.
have hex i:exists x,D x=e (tnth (val lambda) i).
  apply:hRange; by rewrite hEigen hOne scale1r.
have [a hA]:=choice hex.
exists a.
have hSel:orthonormal_family (@euclidean_inner_product R v)
    (fun i:'I_mu=>e (tnth (val lambda) i)).
  by move=>i j; rewrite hOrtho (inj_eq (@Lambda_tnth_injective v mu lambda)).
have hInd:=@orthonormal_independent R (R_n R v) (@euclidean_inner_product R v)
  (@euclidean_inner_productP R v) [the finType of 'I_mu]
  (fun i=>e (tnth (val lambda) i)) hSel.
have hEq:(fun i=>D (a i))=(fun i:'I_mu=>e (tnth (val lambda) i)).
  by apply:funext=>i; exact:hA i.
by rewrite hEq.
Qed.
