(** Federer (1969), 3.2.11, p. 249: the
    cylinder Q=A times B and its double fibres under
    g(x,z)=f(x)+epsilon*z and p(x,z)=z. These are
    exact pointwise set identities before integration. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinearMaps MappingMultiplicity CoareaPerturbationMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coarea_cylinder]: Q=A times B(0,1)
    in Federer 3.2.11, p. 249. This supporting
    product-set notation permits any B and uses the
    existing Cartesian block identification. *)
Definition coarea_cylinder (R:realType) m n (A:set (R_n R m))
    (B:set (R_n R n)):set (R_n R (m+n)):=
  [set w|A (@euclidean_first_block R m n w) /\ B (@euclidean_last_block R m n w)].

(** Source for [coarea_cylinder_pair]: the actual
    membership law of the cylinder in Federer 3.2.11,
    p. 249, supporting the product-measure and fibre calculations. *)
Lemma coarea_cylinder_pair (R:realType) m n (A:set (R_n R m))
    (B:set (R_n R n)) x z:
  coarea_cylinder A B (euclidean_block_join (x,z)) <->A x /\ B z.
Proof.
change (A (euclidean_block_split (euclidean_block_join (x,z))).1 /\
  B (euclidean_block_split (euclidean_block_join (x,z))).2 <->A x /\ B z).
by rewrite euclidean_block_joinK.
Qed.

(** Source for [coarea_perturbation_double_fibre]: the
    equality of the sliced perturbed fibre with the
    translated original fibre in Federer 3.2.11, p. 249.
    The displayed set identity is valid for every y,z,
    including z outside B and empty original fibres. *)
Theorem coarea_perturbation_double_fibre (R:realType) m n
    (f:R_n R m->R_n R n) e (A:set (R_n R m)) (B:set (R_n R n)) y z:
  mapping_fibre (@euclidean_last_block R m n)
    (mapping_fibre (coarea_perturbation_map f e) (coarea_cylinder A B) y) z=
  (fun x=>euclidean_block_join (x,z)) @` [set x|A x /\ B z /\ f x=y-e*:z].
Proof.
apply/seteqP; split=>w.
- move=>[[[hA hB] hG] hQ].
  have hPair:w=euclidean_block_join (@euclidean_first_block R m n w,z).
    rewrite -hQ; exact (Logic.eq_sym (@euclidean_block_splitK R m n w)).
  exists (@euclidean_first_block R m n w); last exact (Logic.eq_sym hPair).
  split; first exact hA.
  split; first by rewrite -hQ; exact hB.
  rewrite hPair coarea_perturbation_map_pair in hG.
  have h:=congr1 (fun v:R_n R n=>v-e*:z) hG.
  by rewrite addrK in h.
- move=>[x [hA [hB hF]] <-]; split.
  + split.
    * apply:(coarea_cylinder_pair A B x z).2; by split.
    * by rewrite coarea_perturbation_map_pair hF subrK.
  + change ((euclidean_block_split (euclidean_block_join (x,z))).2=z).
    by rewrite euclidean_block_joinK.
Qed.
