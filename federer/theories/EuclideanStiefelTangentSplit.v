(** Federer (1969), 3.2.28(2), printed p. 264: the horizontal
    space Z(g), the skew part g* h, and h-g g* h. The algebraic
    kernel is kept distinct from its subsequent geometric tangent
    identification by the regular-level theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerProductLaws AdjointUP AdjointLaws
  AdjointCriteria OrthogonalMaps SymmetricEndomorphisms
  EuclideanRectangularAdjoint EuclideanGramDifferentialAlgebra
  EuclideanGramTangentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_stiefel_horizontal_reverse]: h* g= 0
    iff g* h= 0 by adjoint pairing, supporting Z(g) in
    Federer 3.2.28(2), p. 264. *)
Lemma euclidean_stiefel_horizontal_reverse (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  hom_comp (euclidean_rectangular_adjoint g) h= 0 ->
  hom_comp (euclidean_rectangular_adjoint h) g= 0.
Proof.
move=>hz; apply:hom_ext=>y.
apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
rewrite hom_compE hom_zeroE
  (bil0r (inner_bilinear (@euclidean_inner_productP R m)))
  euclidean_rectangular_adjoint_pairing
  (inner_symmetric (@euclidean_inner_productP R n)).
rewrite -euclidean_rectangular_adjoint_pairing.
have he:euclidean_rectangular_adjoint g (h x)= 0.
  exact:(congr1 (fun f:Hom (R_n R m) (R_n R m)=>f x) hz).
by rewrite he (bil0r (inner_bilinear (@euclidean_inner_productP R m))).
Qed.

(** Source for [euclidean_stiefel_horizontal_kernel]: Z(g) is
    contained in the algebraic tangent kernel, Federer
    3.2.28(2), p. 264. *)
Lemma euclidean_stiefel_horizontal_kernel (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  hom_comp (euclidean_rectangular_adjoint g) h= 0 ->
  euclidean_gram_differential g h= 0.
Proof.
move=>hz; rewrite euclidean_gram_differentialE hz
  (euclidean_stiefel_horizontal_reverse hz) add0r; reflexivity.
Qed.

(** Source for [euclidean_stiefel_horizontal_split]: the
    assertions h-g g* h belongs to Z(g) and g* h is skew,
    and their exact decomposition, Federer 3.2.28(2), p. 264. *)
Theorem euclidean_stiefel_horizontal_split (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  euclidean_gram_differential g h= 0 ->
  let u:=hom_comp (euclidean_rectangular_adjoint g) h in
  let z:=h-hom_comp g u in
  hom_comp (euclidean_rectangular_adjoint g) z= 0 /\
  is_skewsymmetric_endomorphism (@euclidean_inner_product R m) (hom_as_linear u) /\
  h= z+hom_comp g u.
Proof.
move=>hg hh u z.
have hCan:cancel g (euclidean_rectangular_adjoint g).
  exact:(orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R m)
    (euclidean_rectangular_adjoint_pairing g)).1 hg.
split.
- apply:hom_ext=>x; change (euclidean_rectangular_adjoint g (h x-g (u x))= 0).
  rewrite (linearB (hom_as_linear (euclidean_rectangular_adjoint g))).
  change (euclidean_rectangular_adjoint g (h x)-
    euclidean_rectangular_adjoint g (g (u x))=0).
  by rewrite hCan /u hom_compE subrr.
split; first exact:(euclidean_gram_kernel_skew g h).1 hh.
by rewrite /z subrK.
Qed.

(** Source for [euclidean_stiefel_split_unique]: the horizontal
    and vertical summands of Federer 3.2.28(2), p. 264,
    intersect trivially. This supporting uniqueness uses only
    orthogonality and the actual equation g* z= 0. *)
Lemma euclidean_stiefel_split_unique (R:realType) m n
    (g z:Hom (R_n R m) (R_n R n)) (u:Hom (R_n R m) (R_n R m)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  hom_comp (euclidean_rectangular_adjoint g) z= 0 ->
  z+hom_comp g u= 0 ->z= 0 /\ u= 0.
Proof.
move=>hg hz he.
have hCan:cancel g (euclidean_rectangular_adjoint g).
  exact:(orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R m)
    (euclidean_rectangular_adjoint_pairing g)).1 hg.
have hu:u= 0.
  apply:hom_ext=>x.
  have hEq:=congr1 (fun f:Hom (R_n R m) (R_n R n)=>
    euclidean_rectangular_adjoint g (f x)) he.
  have hZ:=congr1 (fun f:Hom (R_n R m) (R_n R m)=>f x) hz.
  change (euclidean_rectangular_adjoint g (z x)=0) in hZ.
  change (euclidean_rectangular_adjoint g (z x+g (u x))=
    euclidean_rectangular_adjoint g 0) in hEq.
  rewrite (linearD (hom_as_linear (euclidean_rectangular_adjoint g)))
    (linear0 (hom_as_linear (euclidean_rectangular_adjoint g))) in hEq.
  change (euclidean_rectangular_adjoint g (z x)+
    euclidean_rectangular_adjoint g (g (u x))=0) in hEq.
  by rewrite hCan hZ add0r in hEq.
split=>//.
have hc:hom_comp g u= 0 by apply:hom_ext=>x; rewrite hom_compE hu hom_zeroE linear0.
by rewrite hc addr0 in he.
Qed.
