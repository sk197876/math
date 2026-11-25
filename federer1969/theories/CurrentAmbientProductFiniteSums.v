(** Federer (1969), 4.1.11, p. 366: expand
    the original Cartesian current product over the
    finite face and simplex sums. This reuses the
    proved bilinearity of 4.1.8, p. 361, and
    the existing finite-sum morphism law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentAmbientCartesianProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentAmbientProductFiniteSums.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation CA := (@current_space R h2 m (Full m) (hFull m) i).
Local Notation CB := (@current_space R h2 n (Full n) (hFull n) j).
Local Notation Product := (@current_ambient_cartesian_product R h2 m n i j).
Local Notation hProduct := (@current_ambient_cartesian_product_bilinear R h2 m n i j).

(** Source for [current_ambient_product_first_weighted_sum]:
    the original product distributes over a finite
    weighted first factor, supporting the rectangular
    decomposition in Federer 4.1.11, p. 366. The
    index type may be empty and all weights are allowed. *)
Theorem current_ambient_product_first_weighted_sum (I:finType)
    (a:I->R) (S:I->CA) (T:CB):
  Product (\sum_k a k*:S k) T=\sum_k a k*:Product (S k) T.
Proof.
rewrite (big_morph (fun V=>Product V T) (fun V W=>bilDl hProduct V W T) (bil0l hProduct T)).
apply:eq_bigr=>k _;exact:(bilZl hProduct (a k) (S k) T).
Qed.

(** Source for [current_ambient_product_second_weighted_sum]:
    the original product distributes over every finite
    signed second factor, supporting the prism boundary
    induction in Federer 4.1.11, p. 366. No
    representation or compactness condition is needed. *)
Theorem current_ambient_product_second_weighted_sum (I:finType)
    (S:CA) (a:I->R) (T:I->CB):
  Product S (\sum_k a k*:T k)=\sum_k a k*:Product S (T k).
Proof.
rewrite (big_morph (fun V=>Product S V) (bilDr hProduct S) (bil0r hProduct S)).
apply:eq_bigr=>k _;exact:(bilZr hProduct (a k) S (T k)).
Qed.
End CurrentAmbientProductFiniteSums.
