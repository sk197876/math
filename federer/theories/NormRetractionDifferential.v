(** Federer (1969), 3.1.20, p. 233: differentiating f composed
    with f=f gives Df[f(x)] Df(x)=Df(x). At fixed points Df is a
    projection, acting identically on its actual linear image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialChain NormDifferentialDirectional NormClassOneUP NormRegularity RetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RetractionDifferential.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variables (A B:set X) (f:X->X) (D:X->Hom X X) (k:nat).
Hypothesis hR:is_norm_class_retraction hNX A B f k.
Hypothesis hD:is_norm_class_one_field NX NX A f D.

(** Source for [norm_retraction_idempotent]: f composed with f=f
    on its actual domain, the first observation of the converse
    proof in Federer 3.1.20, p. 233. *)
Lemma norm_retraction_idempotent x : A x -> f (f x)=f x.
Proof.
move=>hx; exact (@norm_retraction_fixed R X NX hNX A B f k hR (f x)
  (@norm_retraction_range R X NX hNX A B f k hR x hx)).
Qed.

(** Source for [norm_retraction_differential_composite]: the first
    displayed differential identity in the converse of Federer
    3.1.20, p. 233. Its actual composite domain reduces to A
    because f(A) is contained in B, and B is contained in A. *)
Lemma norm_retraction_differential_composite x : A x ->
  hom_comp (D (f x)) (D x)=D x.
Proof.
move=>hx.
have hmap y (hy:A y):A (f y).
  exact (@norm_retraction_subset R X NX hNX A B f k hR (f y)
    (@norm_retraction_range R X NX hNX A B f k hR y hy)).
have hdx:=@norm_class_one_differential R X X NX NX A f D hD x hx.
have hdfx:=@norm_class_one_differential R X X NX NX A f D hD (f x) (hmap x hx).
have hchain:=norm_differential_chain hNX hNX hNX hdx hdfx.
have hd:=@norm_differential_restrict R X X NX NX
  (fun y=>A y /\ A (f y)) A (fun y=>f (f y)) x (hom_comp (D (f x)) (D x))
  (fun y hy=>conj hy (hmap y hy)) (norm_differential_interior hdx) hchain.
have hagree:=@norm_differential_domain_agreement R X X NX NX hNX A
  (fun y=>f (f y)) f x (hom_comp (D (f x)) (D x))
  (fun y hy=>@norm_retraction_idempotent y hy) hd.
exact (@norm_differential_unique R X X NX NX hNX hNX A f x
  (hom_comp (D (f x)) (D x)) (D x) hagree hdx).
Qed.

(** Source for [norm_retraction_differential_image]: image Df(x)
    is contained in image Df[f(x)], the first displayed inclusion
    of the converse proof in Federer 3.1.20, p. 233. *)
Lemma norm_retraction_differential_image x : A x -> forall y,
  (exists v, D x v=y) -> exists w, D (f x) w=y.
Proof.
move=>hx y [v <-]; exists (D x v).
have hh:=congr1 (fun L:Hom X X=>L v) (norm_retraction_differential_composite hx).
exact hh.
Qed.

(** Source for [norm_retraction_differential_idempotent]: at a
    point b of B the differential is idempotent, supporting the
    exterior-norm criterion on Federer 3.1.20, p. 233. *)
Lemma norm_retraction_differential_idempotent b : B b -> hom_comp (D b) (D b)=D b.
Proof.
move=>hb.
have hbA:=@norm_retraction_subset R X NX hNX A B f k hR b hb.
have hh:=norm_retraction_differential_composite hbA.
by rewrite (@norm_retraction_fixed R X NX hNX A B f k hR b hb) in hh.
Qed.

(** Source for [norm_retraction_differential_fixed_range]: Df(b)
    fixes every vector in its image, the second displayed identity
    in the converse of Federer 3.1.20, p. 233. *)
Lemma norm_retraction_differential_fixed_range b : B b -> forall v,
  (exists w, D b w=v) -> D b v=v.
Proof.
move=>hb v [w <-].
exact (congr1 (fun L:Hom X X=>L w) (norm_retraction_differential_idempotent hb)).
Qed.
End RetractionDifferential.
