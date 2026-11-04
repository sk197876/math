(** Federer (1969), 3.1.1(2), p. 210: actual
    differentials of composites and Cartesian pairs, supporting
    the product tangent calculation in 3.2.47, p. 283.
    The Cartesian norm is the existing sealed inner-product norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP InnerProductUP InnerNorm HilbertFormCompactness
  ProductInner ProductInnerPairRegularity RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialChain NormDifferentialLocal NormDifferentialArithmetic
  NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_compose_on]: the chain
    rule 3.1.1(2), p. 210, on an original
    domain whose image lies in the second domain;
    supporting 3.2.47, p. 283. *)
Lemma norm_differential_compose_on (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->Z) a (L:Hom X Y) (M:Hom Y Z):
  (forall x,A x ->B (f x)) ->
  has_norm_differential NX NY A f a L ->
  has_norm_differential NY NZ B g (f a) M ->
  has_norm_differential NX NZ A (fun x=>g (f x)) a (hom_comp M L).
Proof.
move=>hMap hf hg.
exact (@norm_differential_restrict R X Z NX NZ (fun x=>A x /\B (f x)) A
  (fun x=>g (f x)) a (hom_comp M L) (fun x hx=>conj hx (hMap x hx))
  (norm_differential_interior hf) (norm_differential_chain hNX hNY hNZ hf hg)).
Qed.

(** Source for [norm_differential_postcompose_linear]: the
    linear case of 3.1.1(2), p. 210, supporting
    actual Cartesian coordinate differentials in 3.2.47, p. 283. *)
Lemma norm_differential_postcompose_linear (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (f:X->Y) a (L:Hom X Y) (M:Hom Y Z):
  norm_bounded_linear NY NZ M ->has_norm_differential NX NY A f a L ->
  has_norm_differential NX NZ A (fun x=>M (f x)) a (hom_comp M L).
Proof.
move=>hM hf.
exact (@norm_differential_compose_on R X Y Z NX NY NZ hNX hNY hNZ A (fun _=>True)
  f M a L M (fun x _=>I) hf
  (@norm_differential_linear R Y Z NY NZ hNY hNZ (fun _=>True) (f a) M
    (norm_full_domain_interior NY (f a)) hM)).
Qed.

(** Source for [product_pair_hom]: pairing the actual linear
    coordinate differentials, supporting 3.2.47, p. 283,
    by the linear Cartesian identification of 1.1.2, pp. 9–10. *)
Definition product_pair_hom (R:realType) (X V W:lmodType R)
    (L:Hom X V) (M:Hom X W):Hom X [the lmodType R of (V*W)%type]:=
  hom_comp (@product_first_injection_hom R V W) L+
    hom_comp (@product_second_injection_hom R V W) M.

(** Source for [product_pair_homE]: the two original
    coordinate values of the paired differential, supporting
    3.2.47, p. 283. *)
Lemma product_pair_homE (R:realType) (X V W:lmodType R)
    (L:Hom X V) (M:Hom X W) x:product_pair_hom L M x=(L x,M x).
Proof.
change ((L x+0,0+M x)=(L x,M x)).
by rewrite addr0 add0r.
Qed.

(** Source for [norm_differential_inner_pair]: the differential
    of a Cartesian pair is the pair of differentials,
    by 3.1.1(2), p. 210, and linearity;
    supporting the actual tangent computation in 3.2.47, p. 283. *)
Theorem norm_differential_inner_pair (R:realType) (X V W:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) BV BW
    (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    (A:X->Prop) (f:X->V) (g:X->W) a (L:Hom X V) (M:Hom X W):
  has_norm_differential NX (inner_norm hV) A f a L ->
  has_norm_differential NX (inner_norm hW) A g a M ->
  has_norm_differential NX (inner_norm (product_inner_productP hV hW)) A
    (fun x=>(f x,g x)) a (product_pair_hom L M).
Proof.
move=>hf hg.
pose P:lmodType R:=[the lmodType R of (V*W)%type].
pose hNV:=inner_norm_real_norm hV.
pose hNW:=inner_norm_real_norm hW.
pose hNP:=inner_norm_real_norm (product_inner_productP hV hW).
pose i:=@product_first_injection_hom R V W.
pose j:=@product_second_injection_hom R V W.
have hI:norm_bounded_linear (inner_norm hV) (inner_norm (product_inner_productP hV hW)) i.
  exists 1; split; first exact:ler01.
  by move=>v; rewrite (@product_first_injection_norm R V W BV BW hV hW) mul1r.
have hJ:norm_bounded_linear (inner_norm hW) (inner_norm (product_inner_productP hV hW)) j.
  exists 1; split; first exact:ler01.
  by move=>w; rewrite (@product_second_injection_norm R V W BV BW hV hW) mul1r.
have hLeft:=@norm_differential_postcompose_linear R X V P NX _ _ hNX hNV hNP A f a L i hI hf.
have hRight:=@norm_differential_postcompose_linear R X W P NX _ _ hNX hNW hNP A g a M j hJ hg.
have hSum:=@norm_differential_add R X P NX _ hNP A (fun x=>i (f x)) (fun x=>j (g x))
  a (hom_comp i L) (hom_comp j M) hLeft hRight.
have hPair:(fun x=>(f x,g x))=(fun x=>i (f x)+j (g x)).
  apply:funext=>x; change ((f x,g x)=(f x+0,0+g x)).
  by rewrite addr0 add0r.
by rewrite -hPair in hSum.
Qed.
