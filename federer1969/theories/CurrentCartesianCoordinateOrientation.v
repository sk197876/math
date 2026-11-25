(** Federer (1969), 4.1.8, p. 362: the
    ordered product of the original coordinate
    orientations is the original coordinate orientation
    in the concatenated Euclidean space. Reuse the
    existing block maps and exterior word laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom AlgebraUP GradedComponents GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps ConcatenatedFamilies ExteriorAlgebra ExteriorGrading
  ExteriorMaps FiniteExteriorPowers ExteriorHomogeneousProducts CurrentCartesianVectorProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_cartesian_first_coordinate_basis]: the
    original first injection sends each first-factor
    coordinate vector to its original first-block
    coordinate vector, supporting Federer 4.1.8,
    p. 362, by 2.6.5, p. 120. *)
Lemma current_cartesian_first_coordinate_basis (R:realType) m n (i:'I_m):
  @euclidean_first_injection_map R m n (@coordinate_basis R m i)=
    @coordinate_basis R (m+n) (lshift n i).
Proof.
apply/ffunP=>j;case:(split_ordP j)=>k->.
- change (euclidean_block_join (@coordinate_basis R m i,(0:R_n R n)) (lshift n k)=
    @coordinate_basis R (m+n) (lshift n i) (lshift n k)).
  by rewrite euclidean_block_join_left /coordinate_basis !ffunE eq_lshift.
- change (euclidean_block_join (@coordinate_basis R m i,(0:R_n R n)) (rshift m k)=
    @coordinate_basis R (m+n) (lshift n i) (rshift m k)).
  by rewrite euclidean_block_join_right /coordinate_basis !ffunE eq_rlshift.
Qed.

(** Source for [current_cartesian_last_coordinate_basis]: the
    original second injection sends each second-factor
    coordinate vector to its original last-block
    coordinate vector, supporting Federer 4.1.8,
    p. 362, by 2.6.5, p. 120. *)
Lemma current_cartesian_last_coordinate_basis (R:realType) m n (i:'I_n):
  @euclidean_last_injection_map R m n (@coordinate_basis R n i)=
    @coordinate_basis R (m+n) (rshift m i).
Proof.
apply/ffunP=>j;case:(split_ordP j)=>k->.
- change (euclidean_block_join ((0:R_n R m),@coordinate_basis R n i) (lshift n k)=
    @coordinate_basis R (m+n) (rshift m i) (lshift n k)).
  by rewrite euclidean_block_join_left /coordinate_basis !ffunE eq_lrshift.
- change (euclidean_block_join ((0:R_n R m),@coordinate_basis R n i) (rshift m k)=
    @coordinate_basis R (m+n) (rshift m i) (rshift m k)).
  by rewrite euclidean_block_join_right /coordinate_basis !ffunE eq_rshift.
Qed.

(** Source for [current_cartesian_coordinate_orientation]: the
    original Lambda_m P(e_1 wedge ... wedge e_m)
    wedge Lambda_n Q(e_1 wedge ... wedge e_n)
    is precisely the concatenated coordinate top vector,
    supporting the Euclidean-current product in Federer
    4.1.8, p. 362. Both zero-dimensional endpoints
    use the original exterior units. *)
Theorem current_cartesian_coordinate_orientation (R:realType) m n:
  @current_cartesian_vector_product R m n m n
    (e_lambda (@coordinate_basis R m) (ord_tuple m))
    (e_lambda (@coordinate_basis R n) (ord_tuple n))=
    e_lambda (@coordinate_basis R (m+n)) (ord_tuple (m+n)).
Proof.
pose P:=hom_as_linear (@euclidean_first_injection_map R m n).
pose Q:=hom_as_linear (@euclidean_last_injection_map R m n).
have hSequence:[seq P (@coordinate_basis R m i)|i<-enum 'I_m]++
    [seq Q (@coordinate_basis R n i)|i<-enum 'I_n]=
    [seq @coordinate_basis R (m+n) i|i<-enum 'I_(m+n)].
  rewrite -concatenate_family_sequence;apply:eq_map=>i.
  case:(split_ordP i)=>j->.
  - rewrite concatenate_family_l;exact:current_cartesian_first_coordinate_basis.
  - rewrite concatenate_family_r;exact:current_cartesian_last_coordinate_basis.
apply:val_inj.
change (wedge
    (exterior_algebra_map P (component_val (e_lambda (@coordinate_basis R m) (ord_tuple m))))
    (exterior_algebra_map Q (component_val (e_lambda (@coordinate_basis R n) (ord_tuple n))))=
  component_val (e_lambda (@coordinate_basis R (m+n)) (ord_tuple (m+n)))).
rewrite !e_lambdaE !exterior_algebra_map_word exterior_word_cat -!map_comp.
rewrite !enumT in hSequence.
exact:(congr1 (@exterior_word R (R_n R (m+n))) hSequence).
Qed.
