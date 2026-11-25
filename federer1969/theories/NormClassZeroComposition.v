(** Federer (1969), 3.1.11, p. 220:
    continuity of composition on its actual open
    domain, the base of the class-k induction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_composite_interior]:
    the domain of a composite of continuous
    maps with open domains is open, supporting
    Federer 3.1.11, p. 220. No
    global inclusion of f(A) in B is required. *)
Lemma norm_class_zero_composite_interior (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->Z) :
  norm_class_zero NX NY A f -> norm_class_zero NY NZ B g ->
  forall a, A a /\ B (f a) ->
    norm_domain_interior NX (fun x=>A x /\ B (f x)) a.
Proof.
move=> hf hg a [ha hb].
have [r [hr hA]] := (hf a ha).1.
have [s [hs hB]] := (hg (f a) hb).1.
have [d [hd hcont]] := (hf a ha).2 s hs.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=> h; rewrite lt_min=>/andP [hhr hhd].
have hah := hA h hhr; split=> //.
have hh := hB (f (a+h)-f a) (hcont h hah hhd).
by rewrite addrC subrK in hh.
Qed.

(** Source for [norm_class_zero_composition]:
    the class-zero case of composition preserving
    class k in Federer 3.1.11,
    p. 220. The domain remains exactly
    the points of A mapped into B. *)
Theorem norm_class_zero_composition (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->Z) :
  norm_class_zero NX NY A f -> norm_class_zero NY NZ B g ->
  norm_class_zero NX NZ (fun x=>A x /\ B (f x)) (fun x=>g (f x)).
Proof.
move=> hf hg a [ha hb]; split.
- exact (@norm_class_zero_composite_interior R X Y Z NX NY NZ A B f g
    hf hg a (conj ha hb)).
- move=> e he.
  have [dg [hdg hgc]] := (hg (f a) hb).2 e he.
  have [df [hdf hfc]] := (hf a ha).2 dg hdg.
  exists df; split=> // h [hah hbh] hh.
  have heq : f a+(f (a+h)-f a)=f (a+h) by rewrite addrC subrK.
  have hBinc : B (f a+(f (a+h)-f a)) by rewrite heq.
  have hvalue := hgc (f (a+h)-f a) hBinc (hfc h hah hh).
  by rewrite heq in hvalue.
Qed.
