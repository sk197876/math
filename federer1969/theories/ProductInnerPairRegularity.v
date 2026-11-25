(** Federer (1969), 1.7.11, p. 36, and
    3.2.47, pp. 282–283: actual Cartesian inner
    coordinates for the local sphere product parametrizations.
    The two linear inclusions have their actual norm one;
    pairing class-k maps follows by linear composition and
    addition. No replacement product norm is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom InnerProductUP InnerNorm ProductInner Bilinear
  HilbertFormCompactness RealNormUP NormDifferentialUP NormRegularity
  NormRegularityOperations NormRegularityLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [product_first_injection_hom]: the actual
    linear inclusion v to (v,0) for 1.7.11, p. 36,
    supporting the product coordinates in 3.2.47, p. 283. *)
Definition product_first_injection_hom (R:realType) (V W:lmodType R):
    Hom V [the lmodType R of (V*W)%type].
Proof.
apply:(@HomMap R V [the lmodType R of (V*W)%type] (fun v=>(v,0))).
apply/asboolP=>c x y.
change ((c*:x+y,0)=(c*:x+y,c*:(0:W)+0)).
by rewrite scaler0 add0r.
Defined.

(** Source for [product_second_injection_hom]: the actual
    linear inclusion w to (0,w) for 1.7.11, p. 36,
    supporting the product coordinates in 3.2.47, p. 283. *)
Definition product_second_injection_hom (R:realType) (V W:lmodType R):
    Hom W [the lmodType R of (V*W)%type].
Proof.
apply:(@HomMap R W [the lmodType R of (V*W)%type] (fun w=>(0,w))).
apply/asboolP=>c x y.
change ((0,c*:x+y)=(c*:(0:V)+0,c*:x+y)).
by rewrite scaler0 add0r.
Defined.

(** Source for [product_first_injection_norm]: the first
    factor inclusion preserves the actual norm of 1.7.11,
    p. 36; supporting 3.2.47, p. 283. *)
Lemma product_first_injection_norm (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) v:
  inner_norm (product_inner_productP hB hC) (@product_first_injection_hom R V W v)=
    inner_norm hB v.
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr product_innerE.
change (B v v=B v v+C 0 0).
by rewrite (bil0l (inner_bilinear hC)) addr0.
Qed.

(** Source for [product_second_injection_norm]: the second
    factor inclusion preserves the actual norm of 1.7.11,
    p. 36; supporting 3.2.47, p. 283. *)
Lemma product_second_injection_norm (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) w:
  inner_norm (product_inner_productP hB hC) (@product_second_injection_hom R V W w)=
    inner_norm hC w.
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr product_innerE.
change (C w w=B 0 0+C w w).
by rewrite (bil0l (inner_bilinear hB)) add0r.
Qed.

(** Source for [norm_class_inner_pair]: pairing two actual
    class-k maps preserves class k in the Cartesian inner
    metric, supporting the E times I parametrizations of
    3.2.47, p. 283. The source and both factors
    may have arbitrary dimension. *)
Theorem norm_class_inner_pair (R:realType) (X V W:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) B C
    (hB:@is_inner_product R V B) (hC:@is_inner_product R W C)
    (A:set X) (f:X->V) (g:X->W) k:
  norm_class hNX (inner_norm_real_norm hB) A f k ->
  norm_class hNX (inner_norm_real_norm hC) A g k ->
  norm_class hNX (inner_norm_real_norm (product_inner_productP hB hC)) A
    (fun x=>(f x,g x)) k.
Proof.
move=>hf hg.
pose P:lmodType R:=[the lmodType R of (V*W)%type].
pose hNV:=inner_norm_real_norm hB.
pose hNW:=inner_norm_real_norm hC.
pose hNP:=inner_norm_real_norm (product_inner_productP hB hC).
pose i:=@product_first_injection_hom R V W.
pose j:=@product_second_injection_hom R V W.
have hI:norm_bounded_linear (inner_norm hB) (inner_norm (product_inner_productP hB hC)) i.
  exists 1; split; first exact:ler01.
  by move=>v; rewrite (@product_first_injection_norm R V W B C hB hC) mul1r.
have hJ:norm_bounded_linear (inner_norm hC) (inner_norm (product_inner_productP hB hC)) j.
  exists 1; split; first exact:ler01.
  by move=>w; rewrite (@product_second_injection_norm R V W B C hB hC) mul1r.
have hLeft:=@norm_class_postcompose_linear R X V P NX _ _ hNX hNV hNP A f i k hI hf.
have hRight:=@norm_class_postcompose_linear R X W P NX _ _ hNX hNW hNP A g j k hJ hg.
have hSum:=@norm_class_add R X P NX _ hNX hNP A (fun x=>i (f x)) (fun x=>j (g x)) k hLeft hRight.
have hPair:(fun x=>(f x,g x))=(fun x=>i (f x)+j (g x)).
  apply:funext=>x.
  change ((f x,g x)=(f x+0,0+g x)).
  by rewrite addr0 add0r.
by rewrite -hPair in hSum.
Qed.
