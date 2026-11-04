(** Federer (1969), 3.2.47, p. 282: differentiability of
    the positively normalized residuals. Every finite class is
    retained, using the actual inner norm and prior scalar calculus. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormClassOneUP
  InnerProductUP InnerProductLaws InnerNorm InnerNormalization InnerNormInequalities
  HilbertFormCompactness NormBoundedBilinearUP NormRegularity NormRegularityOperations
  NormRegularityBilinear ScalarNormalizationRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_product_norm_bounded_bilinear]: continuity
    of the actual inner-product evaluations in the recurrence of
    3.2.47, p. 282, by Cauchy's inequality, 1.7.1, p. 28. *)
Lemma inner_product_norm_bounded_bilinear (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B):
  norm_bounded_bilinear (inner_norm hB) (inner_norm hB) (fun t:R^o=>`|t|) B.
Proof.
split; first exact:inner_bilinear.
exists 1; split; first exact:ler01.
move=>u v; rewrite mul1r; exact:inner_cauchy.
Qed.

(** Source for [inner_norm_nonzero_norm_class]: every differentiability
    class of a nonvanishing residual is preserved by its length,
    supporting the denominator in 3.2.47, p. 282. *)
Lemma inner_norm_nonzero_norm_class (R:realType) (X V:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) B (hB:@is_inner_product R V B)
    (A:X->Prop) (f:X->V) k:
  norm_class hNX (inner_norm_real_norm hB) A f k ->
  (forall x,A x->f x!=0) ->
  norm_class hNX (scalar_absolute_value_norm R) A (fun x=>inner_norm hB (f x)) k.
Proof.
move=>hf hNonzero.
pose N:=inner_norm hB.
pose hN:=inner_norm_real_norm hB.
pose hAbs:=scalar_absolute_value_norm R.
pose q:=fun x=>B (f x) (f x).
have hSquared:=@norm_class_bilinear R X V V R^o NX N N (fun t:R^o=>`|t|)
  hNX hN hN hAbs A f f B k (inner_product_norm_bounded_bilinear hB) hf hf.
have hPositive x:A x->0<q x by move=>hx; rewrite /q (inner_positive hB) hNonzero.
have hOpen x (hx:A x):norm_domain_interior NX A x:=(@norm_class_continuous R X V NX N hNX hN A f k hf x hx).1.
have hBoth:=@norm_class_composition R X R^o R^o NX
  (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) hNX hAbs hAbs A
  (fun t:R^o=>0<t) q Num.sqrt k hSquared (scalar_square_root_norm_class R k).
have hRoot:=@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|)
  hNX hAbs (fun x=>A x /\ 0<q x) A (fun x=>Num.sqrt (q x)) k
  (fun x hx=>conj hx (@hPositive x hx)) hOpen hBoth.
apply:(@norm_class_domain_agreement R X R^o NX (fun t:R^o=>`|t|)
  hNX hAbs A (fun x=>Num.sqrt (q x)) (fun x=>N (f x)) k _ hRoot).
move=>x hx; apply:esym; apply:inner_norm_value; first exact:sqrtr_ge0.
exact:sqr_sqrtr (ltW (@hPositive x hx)).
Qed.

(** Source for [inner_normalize_norm_class]: the exact positive
    normalization v/|v| in 3.2.47, p. 282, preserves each
    finite differentiability class on its actual nonzero domain.
    No differentiability of a choice operation is used. *)
Lemma inner_normalize_norm_class (R:realType) (X V:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) B (hB:@is_inner_product R V B)
    (A:X->Prop) (f:X->V) k:
  norm_class hNX (inner_norm_real_norm hB) A f k ->
  (forall x,A x->f x!=0) ->
  norm_class hNX (inner_norm_real_norm hB) A (fun x=>inner_normalize hB (f x)) k.
Proof.
move=>hf hNonzero.
pose hAbs:=scalar_absolute_value_norm R.
pose N:=inner_norm hB.
pose hN:=inner_norm_real_norm hB.
have hLength:=inner_norm_nonzero_norm_class hf hNonzero.
have hLengthNonzero x (hx:A x):N (f x)!=0.
  by rewrite /N inner_norm_eq0; exact:hNonzero x hx.
have hOpen x (hx:A x):norm_domain_interior NX A x:=(@norm_class_continuous R X V NX N hNX hN A f k hf x hx).1.
have hBoth:=@norm_class_composition R X R^o R^o NX
  (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) hNX hAbs hAbs A
  (fun t:R^o=>t!=0) (fun x=>N (f x)) (fun t=>t^-1) k hLength
  (scalar_reciprocal_norm_class R k).
have hInverse:=@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|)
  hNX hAbs (fun x=>A x /\ N (f x)!=0) A (fun x=>(N (f x))^-1) k
  (fun x hx=>conj hx (@hLengthNonzero x hx)) hOpen hBoth.
exact (@norm_class_scalar_product R X V NX N hNX (inner_norm_real_norm hB)
  A (fun x=>(N (f x))^-1) f k hInverse hf).
Qed.
