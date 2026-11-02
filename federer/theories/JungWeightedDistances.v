(** Federer (1969), 2.10.41, printed p. 200: expand the weighted squared
    distances between the contact centres, bound each off-diagonal term by
    the squared source diameter, then sum over the contact indices. The
    identities below hold in any real inner-product space with the supplied
    finite family. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import InnerProductUP InnerNorm Bilinear BilinearNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_spherical_pair_square]: supporting
    identity |a_i-a_j| squared = 2c squared minus
    2 a_i dot a_j in 2.10.41, p. 200,
    when both vectors have norm c. *)
Lemma inner_spherical_pair_square (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (x y : V) (c : R) :
  inner_norm hB x=c -> inner_norm hB y=c ->
  inner_norm hB (x-y)^+2= 2*c^+2-2*B x y.
Proof.
move=> hx hy.
have hxx : B x x=c^+2 by rewrite -(inner_norm_sqr hB) hx.
have hyy : B y y=c^+2 by rewrite -(inner_norm_sqr hB) hy.
rewrite inner_norm_sqr (bilBl (inner_bilinear hB)) !(bilBr (inner_bilinear hB))
  (inner_symmetric hB y x) hxx hyy; ring.
Qed.

(** Source for [inner_convex_spherical_pair_identity]: direct
    weighted identity 2c squared = sum_i lambda_i
    |a_i-a_j| squared in 2.10.41, p. 200.
    The vectors are translated so their weighted
    barycentre is zero, as in the printed proof. *)
Lemma inner_convex_spherical_pair_identity (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (I : finType)
    (v : I -> V) (w : I -> R) (c : R) :
  (forall i, inner_norm hB (v i)=c) -> (\sum_i w i= 1) ->
  (\sum_i w i*:v i=0) -> forall j,
  \sum_i w i*inner_norm hB (v i-v j)^+2= 2*c^+2.
Proof.
move=> hv hw hmean j.
have hdot : \sum_i w i*B (v i) (v j)=0.
  have hh := congr1 (fun x=>B x (v j)) hmean.
  rewrite (big_morph (fun x=>B x (v j))
    (fun x y=>bilDl (inner_bilinear hB) x y (v j)) (bil0l (inner_bilinear hB) (v j)))
    (bil0l (inner_bilinear hB)) in hh.
  move: hh; under eq_bigr do rewrite (bilZl (inner_bilinear hB)).
  by [].
have he : (\sum_i w i*inner_norm hB (v i-v j)^+2)=
    (\sum_i w i)*(2*c^+2)-2*(\sum_i w i*B (v i) (v j)).
  rewrite mulr_suml mulr_sumr -sumrB; apply: eq_bigr=> i _.
  rewrite (@inner_spherical_pair_square R V B hB (v i) (v j) c (hv i) (hv j)); ring.
by rewrite he hw hdot mul1r mulr0 subr0.
Qed.

(** Source for [inner_convex_spherical_jung_count]: direct
    summed inequality 2k c squared <= (k-1) d squared
    in 2.10.41, p. 200, using k contact centres.
    The zero diagonal is omitted before the diameter
    bound, retaining the sharp constant. Weights may
    vanish and contact centres may repeat. *)
Theorem inner_convex_spherical_jung_count (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) k
    (v : 'I_k -> V) (w : 'I_k -> R) (c d : R) :
  0<=d -> (forall i, 0<=w i) -> (\sum_i w i= 1) -> (\sum_i w i*:v i=0) ->
  (forall i, inner_norm hB (v i)=c) ->
  (forall i j, inner_norm hB (v i-v j)<=d) ->
  2*k%:R*c^+2<=(k%:R-1)*d^+2.
Proof.
move=> hd hw hsum hmean hv hdiam.
have hper j : 2*c^+2<=(1-w j)*d^+2.
  rewrite -(@inner_convex_spherical_pair_identity R V B hB _ v w c hv hsum hmean j).
  rewrite (bigD1 j) //= subrr inner_norm0 expr0n mulr0 add0r.
  have hweights : (\sum_(i | i!=j) w i)= 1-w j.
    have hh := hsum; rewrite (bigD1 j) //= in hh.
    by rewrite -hh addrAC subrr add0r.
  rewrite -hweights mulr_suml; apply: ler_sum=> i hi.
  have hsq : inner_norm hB (v i-v j)^+2<=d^+2.
    by rewrite (ler_sqr (inner_norm_nonnegative hB _) hd).
  exact (ler_wpM2l (hw i) hsq).
have hh : (\sum_(j<k) 2*c^+2)<=(\sum_j (1-w j)*d^+2).
  apply: ler_sum=> j _; exact: hper j.
have hs : (\sum_j (1-w j))=k%:R-1.
  by rewrite sumrB hsum sumr_const card_ord -mulr_natl mulr1.
rewrite -mulr_suml hs sumr_const card_ord -mulr_natl in hh.
nra.
Qed.
