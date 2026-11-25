(** Federer (1969), 3.2.11, p. 249: the
    prescribed perturbation differential (v,w) maps to Dv+epsilon*w.
    Establish its exact block laws and surjectivity before
    deriving the small critical-rank Jacobian estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanBlockLinear
  InnerProductUP InnerProductLaws AdjointLaws Bilinear EuclideanRectangularAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coarea_perturbation_linear]: Dg in
    Federer 3.2.11, p. 249, specified by the printed
    block formula Dg(v,w)=Df(v)+epsilon*w. This is a
    prescribed linear combination of existing coordinate maps. *)
Definition coarea_perturbation_linear (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) (e:R):Hom (R_n R (m+n)) (R_n R n):=
  hom_comp D (@euclidean_first_block_map R m n)+e*:(@euclidean_last_block_map R m n).

(** Source for [coarea_perturbation_linear_pair]: the displayed
    differential formula in Federer 3.2.11, p. 249,
    evaluated on the actual Cartesian block identification. *)
Lemma coarea_perturbation_linear_pair (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) e x z:
  coarea_perturbation_linear D e (euclidean_block_join (x,z))=D x+e*:z.
Proof.
rewrite /coarea_perturbation_linear hom_addE hom_compE hom_scaleE.
change (D ((euclidean_block_split (euclidean_block_join (x,z))).1)+
  e*:(euclidean_block_split (euclidean_block_join (x,z))).2=D x+e*:z).
by rewrite euclidean_block_joinK.
Qed.

(** Source for [coarea_perturbation_linear_surjective]: im Dg=R^n
    in Federer 3.2.11, p. 249. The explicit last-block
    inverse witness works for every nonzero epsilon and every
    D, including critical D and zero-dimensional targets. *)
Lemma coarea_perturbation_linear_surjective (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) e:
  e!=0 ->forall y,exists w,coarea_perturbation_linear D e w=y.
Proof.
move=>he y; exists (euclidean_block_join ((0:R_n R m),e^-1*:y)).
by rewrite coarea_perturbation_linear_pair linear0 add0r scalerA mulfV // scale1r.
Qed.

(** Source for [coarea_perturbation_adjoint_pair]: the covector
    calculation used in Federer 3.2.11, p. 249:
    Dg* a=(Df* a,epsilon*a). Supporting identity proved
    only from the sealed adjoint pairing and block inner products. *)
Lemma coarea_perturbation_adjoint_pair (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) e (a:R_n R n):
  euclidean_rectangular_adjoint (coarea_perturbation_linear D e) a=
    euclidean_block_join (euclidean_rectangular_adjoint D a,e*:a).
Proof.
apply:(inner_vectors_ext (@euclidean_inner_productP R (m+n)))=>x.
rewrite euclidean_rectangular_adjoint_pairing.
have hRight:=@euclidean_block_join_inner R m n (euclidean_block_split x)
  (euclidean_rectangular_adjoint D a,e*:a).
rewrite euclidean_block_splitK in hRight.
rewrite hRight /=.
change (euclidean_inner_product
    (D ((@euclidean_block_split R m n x).1)+e*:(@euclidean_block_split R m n x).2) a=
  euclidean_inner_product (@euclidean_block_split R m n x).1 (euclidean_rectangular_adjoint D a)+
  euclidean_inner_product (@euclidean_block_split R m n x).2 (e*:a)).
by rewrite (bilDl (inner_bilinear (@euclidean_inner_productP R n)))
  (bilZl (inner_bilinear (@euclidean_inner_productP R n)))
  (bilZr (inner_bilinear (@euclidean_inner_productP R n)))
  euclidean_rectangular_adjoint_pairing.
Qed.
